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

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.EdgeContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.StmtContext;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;

final class XcfaEdgeDefinition {

	private final XcfaProcedureSymbol scope;

	private final String source;
	private final String target;
	private final List<XcfaStatement> statements;

	public XcfaEdgeDefinition(final XcfaProcedureSymbol scope, final EdgeContext context) {
		checkNotNull(context);
		this.scope = checkNotNull(scope);

		source = context.source.getText();
		target = context.target.getText();
		statements = createStatements(context.stmts);
	}

	String getSource(){
		return source;
	}
	String getTarget(){
		return target;
	}
	List<XcfaStatement> getStatements() {
		return statements;
	}

	////

	public List<Edge> instantiate(final XCFA.Builder xcfa, final Env env) {
		final XcfaLocationSymbol sourceSymbol = (XcfaLocationSymbol) scope.resolve(source).get();
		final XcfaLocationSymbol targetSymbol = (XcfaLocationSymbol) scope.resolve(target).get();

		final Loc sourceLoc = (Loc) env.eval(sourceSymbol);
		final Loc targetLoc = (Loc) env.eval(targetSymbol);
		final List<Stmt> stmts = statements.stream().map(s -> s.instantiate(env)).collect(Collectors.toList());
		if (stmts.isEmpty()) {
			stmts.add(Stmts.Skip());
		}
		final List<Edge> edges = new ArrayList<>(stmts.size());
		final List<Loc> locs = new ArrayList<>(stmts.size() + 1);
		locs.add(sourceLoc);
		for (int i = 0; i < stmts.size() - 1; ++i) {
			locs.add(xcfa.createLoc(""));
		}
		locs.add(targetLoc);

		for (int i = 0; i < stmts.size(); ++i) {
			edges.add(xcfa.createEdge(locs.get(i), locs.get(i + 1), stmts.get(i)));
		}

		return edges;
	}

	////

	private List<XcfaStatement> createStatements(final List<StmtContext> stmtContexts) {
		final List<XcfaStatement> result = new ArrayList<>();
		for (final StmtContext stmtContext : stmtContexts) {
			final XcfaStatement statement = new XcfaStatement(scope, stmtContext);
			result.add(statement);
		}
		return result;
	}

}
