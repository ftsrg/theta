/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xta.dsl;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xta.Label;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.dsl.XtaVariableSymbol.InstantiateResult;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.ArrayIdContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.CommitContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.FunctionDeclContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.ParameterDeclContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.ParameterIdContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.ProcessDeclContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.StateDeclContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.TypeContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.TypeDeclContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.UrgentContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.VariableDeclContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.VariableIdContext;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

final class XtaProcessSymbol implements Symbol, Scope {

	private final XtaSpecification scope;
	private final SymbolTable symbolTable;

	private final String name;
	private final String initState;
	private final List<XtaParameterSymbol> parameters;
	private final List<XtaVariableSymbol> variables;
	private final List<XtaStateSymbol> states;
	private final List<XtaTransition> transitions;

	public XtaProcessSymbol(final XtaSpecification scope, final ProcessDeclContext context) {
		checkNotNull(context);

		this.scope = checkNotNull(scope);
		symbolTable = new SymbolTable();

		name = context.fId.getText();
		initState = context.fProcessBody.fInit.fId.getText();
		parameters = new ArrayList<>();
		variables = new ArrayList<>();
		states = new ArrayList<>();
		transitions = context.fProcessBody.fTransitions.fTransitions.stream().map(t -> new XtaTransition(this, t))
				.collect(toList());

		declareAllParameters(context.fParameterList.fParameterDecls);
		declareAllTypes(context.fProcessBody.fTypeDecls);
		declareAllVariables(context.fProcessBody.fVariableDecls);
		declareAllFunctions(context.fProcessBody.fFunctionDecls);
		declareAllStates(context.fProcessBody.fStates.fStateDecls, context.fProcessBody.fUrgent,
				context.fProcessBody.fCommit);
	}

	@Override
	public String getName() {
		return name;
	}

	public Set<List<Expr<?>>> getArgumentLists(final Env env) {
		final List<Set<Expr<?>>> argumentValues = parameters.stream().map(p -> p.instantiateValues(env))
				.collect(toList());
		final Set<List<Expr<?>>> argumentLists = Sets.cartesianProduct(argumentValues);
		return argumentLists;
	}

	////

	public XtaProcess instantiate(final XtaSystem system, final String name, final List<? extends Expr<?>> arguments, final Env env) {
		checkArgument(arguments.size() == parameters.size());
		checkArgument(argumentTypesMatch(arguments));

		env.push();
		defineAllParameters(arguments, env);

		final XtaProcess process = system.createProcess(name);
		createAllLocalVariables(process, env);
		createAllStates(process, env);
		createAllTransitions(process, env);

		env.pop();
		return process;
	}

	private void defineAllParameters(final List<? extends Expr<?>> arguments, final Env env) {
		int i = 0;
		for (final XtaParameterSymbol parameter : parameters) {
			final Expr<?> argument = arguments.get(i);
			env.define(parameter, argument);
			i++;
		}
	}

	private void createAllLocalVariables(final XtaProcess process, final Env env) {
		for (final XtaVariableSymbol variable : variables) {
            if (variable.isConstant()) {
                // do nothing; will be defined lazily on first occurrence
            } else {
                final InstantiateResult instantiateResult = variable.instantiate(process.getName() + "_", env);
                if (instantiateResult.isChannel()) {
                    final Label label = instantiateResult.asChannel().getLabel();
                    env.define(variable, label);
                } else if (instantiateResult.isClockVariable()) {
                    final VarDecl<RatType> varDecl = instantiateResult.asClockVariable().getVarDecl();
                    env.define(variable, varDecl);
                    process.getSystem().addClockVar(varDecl);
                } else if (instantiateResult.isDataVariable()) {
                    final VarDecl<?> varDecl = instantiateResult.asDataVariable().getVarDecl();
                    final LitExpr<?> initValue = instantiateResult.asDataVariable().getInitValue();
                    env.define(variable, varDecl);
                    process.getSystem().addDataVar(varDecl, initValue);
                } else {
                    throw new AssertionError();
                }
            }
        }
	}

	private void createAllStates(final XtaProcess process, final Env env) {
		for (final XtaStateSymbol state : states) {
			final Loc loc = state.instantiate(process, env);
			if (state.getName().equals(initState)) {
				process.setInitLoc(loc);
			}
			env.define(state, loc);
		}
	}

	private void createAllTransitions(final XtaProcess process, final Env env) {
		for (final XtaTransition transition : transitions) {
			transition.instantiate(process, env);
		}
	}

	private boolean argumentTypesMatch(final List<? extends Expr<?>> arguments) {
		// TODO
		return true;
	}

	////

	private void declareAllParameters(final List<ParameterDeclContext> contexts) {
		contexts.forEach(this::declare);
	}

	private void declare(final ParameterDeclContext context) {
		final TypeContext typeContext = context.fType;
		for (final ParameterIdContext parameterIdContext : context.fparameterIds) {
			final XtaParameterSymbol parameterSymbol = new XtaParameterSymbol(this, typeContext, parameterIdContext);
			parameters.add(parameterSymbol);
			symbolTable.add(parameterSymbol);
		}
	}

	////

	private void declareAllTypes(final List<TypeDeclContext> contexts) {
		contexts.forEach(this::declare);
	}

	private void declare(final TypeDeclContext context) {
		final TypeContext typeContext = context.fType;
		for (final ArrayIdContext arrayIdContext : context.fArrayIds) {
			final XtaTypeSymbol typeSymbol = new XtaTypeSymbol(this, typeContext, arrayIdContext);
			symbolTable.add(typeSymbol);
		}
	}

	////

	private void declareAllVariables(final List<VariableDeclContext> contexts) {
		contexts.forEach(this::declare);
	}

	private void declare(final VariableDeclContext context) {
		final TypeContext typeContext = context.fType;
		for (final VariableIdContext variableIdContext : context.fVariableIds) {
			final XtaVariableSymbol variableSymbol = new XtaVariableSymbol(this, typeContext, variableIdContext);
			variables.add(variableSymbol);
			symbolTable.add(variableSymbol);
		}
	}

	////

	private void declareAllFunctions(final List<FunctionDeclContext> contexts) {
		contexts.forEach(this::declare);
	}

	private void declare(final FunctionDeclContext context) {
		final XtaFunctionSymbol functionSymbol = new XtaFunctionSymbol(context);
		symbolTable.add(functionSymbol);
	}

	////

	private void declareAllStates(final List<StateDeclContext> contexts, final UrgentContext urgent,
								  final CommitContext commit) {
		contexts.forEach(s -> declare(s, urgent, commit));
	}

	private void declare(final StateDeclContext context, final UrgentContext urgent, final CommitContext commit) {
		final XtaStateSymbol stateSymbol = new XtaStateSymbol(this, context, urgent, commit);
		states.add(stateSymbol);
		symbolTable.add(stateSymbol);
	}

	////

	@Override
	public Optional<XtaSpecification> enclosingScope() {
		return Optional.of(scope);
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		final Optional<Symbol> symbol = symbolTable.get(name);
		if (symbol.isPresent()) {
			return symbol;
		} else {
			return scope.resolve(name);
		}
	}

}
