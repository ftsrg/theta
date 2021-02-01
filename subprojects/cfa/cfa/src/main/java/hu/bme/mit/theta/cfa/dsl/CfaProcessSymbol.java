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
package hu.bme.mit.theta.cfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Builder;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.EdgeContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.LocContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.ProcDeclContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.VarDeclContext;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;

final class CfaProcessSymbol implements Symbol, Scope {

	private final CfaSpecification scope;
	private final SymbolTable symbolTable;

	private final String name;
	private final boolean main;
	private final List<CfaVariableSymbol> variables;
	private final List<CfaLocationSymbol> locations;
	private final List<CfaEdgeDefinition> edges;

	public CfaProcessSymbol(final CfaSpecification scope, final ProcDeclContext context) {
		checkNotNull(context);
		this.scope = checkNotNull(scope);
		symbolTable = new SymbolTable();

		name = context.id.getText();
		main = (context.main != null);
		variables = createVariables(context.varDecls);
		locations = createLocations(context.locs);
		edges = createEdges(context.edges);

		declareAll(variables);
		declareAll(locations);
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isMain() {
		return main;
	}

	////

	public CFA instantiate(final Env env) {
		final Builder cfaBuilder = CFA.builder();
		env.push();

		for (final CfaVariableSymbol variable : variables) {
			final VarDecl<?> var = variable.instantiate();
			env.define(variable, var);
		}

		for (final CfaLocationSymbol location : locations) {
			final Loc loc = location.intantiate(cfaBuilder);
			env.define(location, loc);
		}

		for (final CfaEdgeDefinition edge : edges) {
			edge.instantiate(cfaBuilder, env);
		}

		env.pop();
		return cfaBuilder.build();
	}

	////

	@Override
	public Optional<CfaSpecification> enclosingScope() {
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

	////

	private void declareAll(final Iterable<? extends Symbol> symbols) {
		symbolTable.addAll(symbols);
	}

	private List<CfaVariableSymbol> createVariables(final List<VarDeclContext> varDeclContexts) {
		final List<CfaVariableSymbol> result = new ArrayList<>();
		for (final VarDeclContext varDeclContext : varDeclContexts) {
			final CfaVariableSymbol symbol = new CfaVariableSymbol(varDeclContext);
			result.add(symbol);
		}
		return result;
	}

	private List<CfaLocationSymbol> createLocations(final List<LocContext> locContexts) {
		final List<CfaLocationSymbol> result = new ArrayList<>();

		int nInitLocs = 0;
		int nFinalLocs = 0;
		int nErrorLocs = 0;

		for (final LocContext locContext : locContexts) {
			final CfaLocationSymbol symbol = new CfaLocationSymbol(locContext);

			if (symbol.isInit()) {
				nInitLocs++;
			} else if (symbol.isFinal()) {
				nFinalLocs++;
			} else if (symbol.isError()) {
				nErrorLocs++;
			}

			result.add(symbol);
		}

		checkArgument(nInitLocs == 1, "Exactly one initial location must be specified");
		checkArgument(nFinalLocs <= 1, "At most one final location must be specified");
		checkArgument(nErrorLocs <= 1, "At most one error location must be specified");

		return result;
	}

	private List<CfaEdgeDefinition> createEdges(final List<EdgeContext> edgeContexts) {
		final List<CfaEdgeDefinition> result = new ArrayList<>();
		for (final EdgeContext edgeContext : edgeContexts) {
			final CfaEdgeDefinition edgeDefinition = new CfaEdgeDefinition(this, edgeContext);
			result.add(edgeDefinition);
		}
		return result;
	}

}
