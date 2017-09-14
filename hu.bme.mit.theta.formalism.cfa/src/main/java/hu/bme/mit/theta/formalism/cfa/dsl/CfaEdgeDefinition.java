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
package hu.bme.mit.theta.formalism.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.common.dsl.Environment;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.EdgeContext;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.StmtContext;

final class CfaEdgeDefinition {

	private final CfaProcessSymbol scope;

	private final String source;
	private final String target;
	private final List<CfaStatement> statements;

	public CfaEdgeDefinition(final CfaProcessSymbol scope, final EdgeContext context) {
		checkNotNull(context);
		this.scope = checkNotNull(scope);

		source = context.source.getText();
		target = context.target.getText();
		statements = createStatements(context.stmts);
	}

	////

	public Edge instantiate(final CFA.Builder cfa, final Environment env) {
		final CfaLocationSymbol sourceSymbol = (CfaLocationSymbol) scope.resolve(source).get();
		final CfaLocationSymbol targetSymbol = (CfaLocationSymbol) scope.resolve(target).get();

		final Loc sourceLoc = (Loc) env.eval(sourceSymbol);
		final Loc targetLoc = (Loc) env.eval(targetSymbol);
		final List<Stmt> stmts = statements.stream().map(s -> s.instantiate(env)).collect(toImmutableList());
		final Edge edge = cfa.createEdge(sourceLoc, targetLoc, stmts);
		return edge;
	}

	////

	private List<CfaStatement> createStatements(final List<StmtContext> stmtContexts) {
		final List<CfaStatement> result = new ArrayList<>();
		for (final StmtContext stmtContext : stmtContexts) {
			final CfaStatement statement = new CfaStatement(scope, stmtContext);
			result.add(statement);
		}
		return result;
	}

}
