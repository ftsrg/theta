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

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xta.Label;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.*;
import org.antlr.v4.runtime.Token;

import java.util.*;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

final class XtaSpecification implements Scope {
	private final SymbolTable symbolTable;

	private final List<XtaVariableSymbol> variables;
	private final List<XtaTypeSymbol> types;
	private final List<String> processIds;

	private final XtaSystem system;

	private XtaSpecification(final XtaContext context) {
		checkNotNull(context);
		symbolTable = new SymbolTable();

		variables = new ArrayList<>();
		types = new ArrayList<>();
		processIds = context.fSystem.fIds.stream().map(Token::getText).collect(toList());

		declareAllTypes(context.fTypeDecls);
		declareAllVariables(context.fVariableDecls);
		declareAllFunctions(context.fFunctionDecls);
		declareAllProcesses(context.fProcessDecls);
		declareAllInstantiations(context.fInstantiations);
		system = instantiate();
	}

	public static XtaSpecification fromContext(final XtaContext context) {
		return new XtaSpecification(context);
	}

	public List<XtaVariableSymbol> getVariables() {
		return Collections.unmodifiableList(variables);
	}

	////

	private XtaSystem instantiate() {
		final XtaSystem system = XtaSystem.create();

		final Env env = new Env();

		defineAllTypes(env);
		createAllGlobalVariables(system, env);

		for (final String processId : processIds) {
			final Symbol symbol = symbolTable.get(processId).get();

			if (symbol instanceof XtaProcessSymbol) {
				final XtaProcessSymbol processSymbol = (XtaProcessSymbol) symbol;
				final Set<List<Expr<?>>> argumentLists = processSymbol.getArgumentLists(env);

				for (final List<Expr<?>> argumentList : argumentLists) {
					final String name = createName(processSymbol, argumentList);
					processSymbol.instantiate(system, name, argumentList, env);
				}
			} else if (symbol instanceof XtaInstantiationSymbol) {
				final XtaInstantiationSymbol instantiationSymbol = (XtaInstantiationSymbol) symbol;
				final String procName = instantiationSymbol.getProcName();
				final Optional<Symbol> optSymbol = resolve(procName);
				if (optSymbol.isEmpty()) {
					throw new RuntimeException("Symbol \"" + procName + "\" is undefined.");
				} else {
					Symbol someSymbol = optSymbol.get();
					if (someSymbol instanceof XtaProcessSymbol) {
						final XtaProcessSymbol processSymbol = (XtaProcessSymbol) someSymbol;
						final String name = instantiationSymbol.getName();
						final List<Expr<?>> argumentList = instantiationSymbol.getArgumentList(env);
						processSymbol.instantiate(system, name, argumentList, env);
					} else {
						throw new RuntimeException("Symbol \"" + procName + "\" is not a template.");
					}
				}
			} else {
				throw new AssertionError();
			}
		}

		return system;
	}

	private static String createName(final XtaProcessSymbol processSymbol, final List<Expr<?>> argumentList) {
		final StringBuilder sb = new StringBuilder();
		sb.append(processSymbol.getName());
		argumentList.forEach(a -> sb.append("_" + a.toString()));
		return sb.toString();
	}

	////

	private void defineAllTypes(final Env env) {
		for (final XtaTypeSymbol type : types) {
			env.compute(type, v -> v.instantiate(env));
		}
	}

	private void createAllGlobalVariables(final XtaSystem system, final Env env) {
		for (final XtaVariableSymbol variable : variables) {
			if (variable.isConstant()) {
				// do nothing; will be defined lazily on first occurrence
			} else {
				final XtaVariableSymbol.InstantiateResult instantiateResult = variable.instantiate("", env);
				if (instantiateResult.isChannel()) {
					final Label label = instantiateResult.asChannel().getLabel();
					env.define(variable, label);
				} else if (instantiateResult.isClockVariable()) {
					final VarDecl<RatType> varDecl = instantiateResult.asClockVariable().getVarDecl();
					env.define(variable, varDecl);
					system.addClockVar(varDecl);
				} else if (instantiateResult.isDataVariable()) {
					final VarDecl<?> varDecl = instantiateResult.asDataVariable().getVarDecl();
					final LitExpr<?> initValue = instantiateResult.asDataVariable().getInitValue();
					env.define(variable, varDecl);
					system.addDataVar(varDecl, initValue);
				} else {
					throw new AssertionError();
				}
			}
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
			types.add(typeSymbol);
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

	private void declareAllProcesses(final List<ProcessDeclContext> contexts) {
		contexts.forEach(this::declare);
	}

	private void declare(final ProcessDeclContext context) {
		final XtaProcessSymbol processSymbol = new XtaProcessSymbol(this, context);
		symbolTable.add(processSymbol);
	}

	////

	private void declareAllInstantiations(final List<InstantiationContext> contexts) {
		contexts.forEach(this::declare);
	}

	private void declare(final InstantiationContext context) {
		final XtaInstantiationSymbol processSymbol = new XtaInstantiationSymbol(this, context);
		symbolTable.add(processSymbol);
	}

	////

	public XtaSystem getSystem() {
		return system;
	}

	////

	@Override
	public Optional<Scope> enclosingScope() {
		return Optional.empty();
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		return symbolTable.get(name);
	}

	////

}
