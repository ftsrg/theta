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
package hu.bme.mit.theta.xcfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.ProcDeclContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.SpecContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.VarDeclContext;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;

final class XcfaSpecification implements Scope {

	private final SymbolTable symbolTable;

	private final List<XcfaVariableSymbol> variables;
	private final List<XcfaProcessSymbol> processes;

	private XcfaSpecification(final SpecContext context) {
		checkNotNull(context);
		symbolTable = new SymbolTable();

		variables = createVariables(context.varDecls);
		processes = createProcesses(context.procDecls);

		declareAll(variables);
		declareAll(processes);
	}

	public static XcfaSpecification fromContext(final SpecContext context) {
		return new XcfaSpecification(context);
	}

	////

	public XCFA instantiate() {
		final Env env = new Env();

		for (final XcfaVariableSymbol variable : variables) {
			final VarDecl<?> var = variable.instantiate();
			env.define(variable, var);
		}

		final List<XcfaProcessSymbol> mainProcesses = processes.stream().filter(XcfaProcessSymbol::isMain)
				.collect(toList());

		if (mainProcesses.isEmpty()) {
			throw new IllegalArgumentException("No main process defined");
		} else if (mainProcesses.size() > 1) {
			throw new IllegalArgumentException("More than one main process is defined");
		} else {
			final XcfaProcessSymbol process = Utils.singleElementOf(mainProcesses);
			final XCFA xcfa = process.instantiate(env);
			return xcfa;
		}
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

	private void declareAll(final Iterable<? extends Symbol> symbols) {
		symbolTable.addAll(symbols);
	}

	private List<XcfaVariableSymbol> createVariables(final List<VarDeclContext> varDeclContexts) {
		final List<XcfaVariableSymbol> result = new ArrayList<>();
		for (final VarDeclContext varDeclContext : varDeclContexts) {
			final XcfaVariableSymbol symbol = new XcfaVariableSymbol(varDeclContext);
			result.add(symbol);
		}
		return result;
	}

	private List<XcfaProcessSymbol> createProcesses(final List<ProcDeclContext> procDeclContexts) {
		final List<XcfaProcessSymbol> result = new ArrayList<>();
		for (final ProcDeclContext procDeclContext : procDeclContexts) {
			final XcfaProcessSymbol symbol = new XcfaProcessSymbol(this, procDeclContext);
			result.add(symbol);
		}
		return result;
	}

}
