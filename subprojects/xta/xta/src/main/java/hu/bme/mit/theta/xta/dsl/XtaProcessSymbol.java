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
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xta.Label;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.dsl.XtaVariableSymbol.InstantiateResult;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

final class XtaProcessSymbol implements Symbol, Scope {


	private SymbolTable system_symbolTable;

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
		//this.system_symbolTable = _system_symbolictable;
		name = context.fId.getText();
		initState = context.fProcessBody.fInit.fId.getText();
		parameters = new ArrayList<>();
		variables = new ArrayList<>();
		states = new ArrayList<>();
		transitions = context.fProcessBody.fTransitions.fTransitions.stream().map(t -> new XtaTransition(this, t))
				.collect(toList());

		if (context.fParameterList != null) {
			declareAllParameters(context.fParameterList.fParameterDecls);
		}
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

	public XtaProcess instantiate(final XtaSystem system, final String name, final List<? extends Expr<?>> arguments, final Env env, final SymbolTable _system_symboltable) {
		checkArgument(arguments.size() == parameters.size());
		checkArgument(argumentTypesMatch(arguments));
		env.push();
		system_symbolTable = _system_symboltable;
		defineAllParameters(arguments, env);

		final XtaProcess process = system.createProcess(name);
		//Local variables are handled like global variables signed with Process symbol
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
					env.define_in_parent(variable, label);
                } else if (instantiateResult.isClockVariable()) {
                    final VarDecl<RatType> varDecl = instantiateResult.asClockVariable().getVarDecl();
                    env.define(variable, varDecl);
					env.define_in_parent(variable, varDecl);
                    process.getSystem().addClockVar(varDecl);
                } else if (instantiateResult.isDataVariable()) {
                    final VarDecl<?> varDecl = instantiateResult.asDataVariable().getVarDecl();
                    final LitExpr<?> initValue = instantiateResult.asDataVariable().getInitValue();
                    env.define(variable, varDecl);
					env.define_in_parent(variable, varDecl);
                    process.getSystem().addDataVar(varDecl, initValue);
                } else {
                    throw new AssertionError();
                }
				String backupname = variable.getName();
				variable.setName(process.getName() + "_" + variable.getName());
				if(!system_symbolTable.get(variable.getName()).isPresent()){
					system_symbolTable.add(variable);
				}
				variable.setName(backupname);
            }

        }
	}

	/*private void addSymboltoGlobalScope(XtaProcess process, XtaVariableSymbol var, VarDecl<?> decl){
		if(!system_symbolTable.get(var.getName()).isPresent()){
			var.setName(process.getName() + "_" + var.getName());
			system_symbolTable.add(var);
		}
	}*/

	private void createAllStates(final XtaProcess process, final Env env) {

		for (final XtaStateSymbol state : states) {
			boolean initloc = false;
			final Loc loc = state.instantiate(process, env);
			if (state.getName().equals(initState)) {
				process.setInitLoc(loc);
				initloc = true;
			}
			XtaStateSymbol temp = state.copyAndChangeName(loc.getName());
			env.define(state, loc);
			if(!system_symbolTable.get(temp.getName()).isPresent()){
				env.define_in_parent(temp, loc);
				system_symbolTable.add(temp);
				String varname = loc.getVarName();
				XtaVariableSymbol variableSymbol = XtaVariableSymbol.forcedCreate(varname);
				system_symbolTable.add(variableSymbol);

				VarDecl varDecl = Decls.Var(varname, BoolType.getInstance());
				env.define_in_parent(variableSymbol, varDecl);
				final LitExpr<BoolType> initValue = BoolLitExpr.of(initloc);
				process.getSystem().addDataVar(varDecl, initValue);
			}
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
			//system_symbolTable.add(variableSymbol);
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
