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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import com.google.common.base.Preconditions;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.EdgeContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.LocContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.VarDeclContext;

final class XcfaProcedureSymbol extends InstantiatableSymbol<XCFA.Process.Procedure> implements Scope {

	private final XcfaProcessSymbol scope;
	private final SymbolTable symbolTable;
	private final String name;
	private final boolean main;
	private final Type rtype;
	private final List<XcfaParamSymbol> params;
	private final List<XcfaVariableSymbol> variables;
	private final List<XcfaLocationSymbol> locations;
	private final List<XcfaEdge> edges;
	private XCFA.Process.Procedure procedure = null;
	private boolean startedBuilding = false;
	private Set<CallStmt> incompleteInstantiations;

	XcfaProcedureSymbol(final XcfaProcessSymbol scope, final XcfaDslParser.ProcedureDeclContext context) {
		checkNotNull(context);
		this.scope = checkNotNull(scope);
		symbolTable = new SymbolTable();
		incompleteInstantiations = new HashSet<>();
		name = context.id.getText();
		main = (context.main != null);
		if (context.varDecls != null) {
			variables = createVariables(context.varDecls);
			declareAll(variables);
		} else variables = null;
		if (context.paramDecls != null) {
			params = createParams(context.paramDecls.decls);
			declareAll(params);
		} else params = null;

		locations = createLocations(context.locs);
		declareAll(locations);

		edges = createEdges(context.edges);
		if (context.rtype != null) rtype = new XcfaType(context.rtype).instantiate();
		else rtype = null;
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isMain() {
		return main;
	}

	////

	void addIncompleteInstantiation(CallStmt stmt) {
		incompleteInstantiations.add(stmt);
	}

	public XCFA.Process.Procedure instantiate() {
		if (procedure != null) return procedure;
		else if (startedBuilding) return null;
		startedBuilding = true;
		XCFA.Process.Procedure.Builder builder = XCFA.Process.Procedure.builder();
		builder.setName(name);
		builder.setRtype(rtype);
		if (params != null) params.forEach(xcfaParamSymbol -> builder.createParam(xcfaParamSymbol.instantiate()));
		if (variables != null)
			variables.forEach(xcfaVariableSymbol -> builder.createVar(xcfaVariableSymbol.instantiate()));
		locations.forEach(xcfaLocationSymbol -> {
			XCFA.Process.Procedure.Location loc = xcfaLocationSymbol.instantiate();
			builder.addLoc(loc);
			if (xcfaLocationSymbol.isInit()) builder.setInitLoc(loc);
			else if (xcfaLocationSymbol.isError()) builder.setErrorLoc(loc);
			else if (xcfaLocationSymbol.isFinal()) builder.setFinalLoc(loc);
		});
		edges.forEach(xcfaEdgeDefinition -> builder.addEdge(xcfaEdgeDefinition.instantiate()));
		procedure = builder.build();
		incompleteInstantiations.forEach(callStmt -> {
			Preconditions.checkState(procedure.getParams().size() == callStmt.getParams().size());
			for (int i = 0; i < procedure.getParams().size(); i++) {
				Preconditions.checkState(procedure.getParams().get(i).getType() == callStmt.getParams().get(i).getType());
			}
			callStmt.setProcedure(procedure);
		});
		incompleteInstantiations = null;
		return procedure;
	}

	////

	@Override
	public Optional<XcfaProcessSymbol> enclosingScope() {
		return Optional.of(scope);
	}

	@Override
	public Optional<? extends Symbol> resolve(final String name) {
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

	private List<XcfaVariableSymbol> createVariables(final List<VarDeclContext> varDeclContexts) {
		final List<XcfaVariableSymbol> result = new ArrayList<>();
		for (final VarDeclContext varDeclContext : varDeclContexts) {
			final XcfaVariableSymbol symbol = new XcfaVariableSymbol(varDeclContext);
			result.add(symbol);
		}
		return result;
	}

	private List<XcfaParamSymbol> createParams(final List<XcfaDslParser.DeclContext> declContexts) {
		final List<XcfaParamSymbol> result = new ArrayList<>();
		for (final XcfaDslParser.DeclContext declContext : declContexts) {
			final XcfaParamSymbol symbol = new XcfaParamSymbol(declContext);
			result.add(symbol);
		}
		return result;
	}

	private List<XcfaLocationSymbol> createLocations(final List<LocContext> locContexts) {
		final List<XcfaLocationSymbol> result = new ArrayList<>();

		int nInitLocs = 0;
		int nFinalLocs = 0;
		int nErrorLocs = 0;

		for (final LocContext locContext : locContexts) {
			final XcfaLocationSymbol symbol = new XcfaLocationSymbol(this, locContext);

			if (symbol.isInit()) {
				nInitLocs++;
			} else if (symbol.isFinal()) {
				nFinalLocs++;
			} else if (symbol.isError()) {
				nErrorLocs++;
			}

			for (final XcfaDslParser.CommentContext commentContext : locContext.comments) {
				symbol.addDictionaryEntry(commentContext.id.getText(), commentContext.value.getText());
			}
			result.add(symbol);
		}

		checkArgument(nInitLocs == 1, "Exactly one initial location must be specififed");
		checkArgument(nFinalLocs == 1, "Exactly one final location must be specififed");
		//checkArgument(nErrorLocs == 1, "Exactly one error location must be specififed");

		return result;
	}

	private List<XcfaEdge> createEdges(final List<EdgeContext> edgeContexts) {
		final List<XcfaEdge> result = new ArrayList<>();
		for (final EdgeContext edgeContext : edgeContexts) {
			final XcfaEdge edgeDefinition = new XcfaEdge(this, edgeContext);
			result.add(edgeDefinition);
		}
		return result;
	}

	public String getCanonicalName() {
		return scope.getName() + "::" + getName();
	}
}