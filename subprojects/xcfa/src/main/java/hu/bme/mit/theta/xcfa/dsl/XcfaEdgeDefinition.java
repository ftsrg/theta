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

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.EdgeContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.StmtContext;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

final class XcfaEdgeDefinition {

	private final XcfaProcedureSymbol scope;

	private final String source;
	private final String target;
	private final List<XcfaStatement> statements;

	XcfaEdgeDefinition(final XcfaProcedureSymbol scope, final EdgeContext context) {
		checkNotNull(context);
		this.scope = checkNotNull(scope);

		source = context.source.getText();
		target = context.target.getText();
		statements = createStatements(context.stmts);
	}

	////

	public XCFA.Process.Procedure.Edge instantiate() {
		final XcfaLocationSymbol sourceSymbol = (XcfaLocationSymbol) scope.resolve(source).get();
		final XcfaLocationSymbol targetSymbol = (XcfaLocationSymbol) scope.resolve(target).get();
		return null;
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

	public List<XcfaStatement> getStatements() {
		return statements;
	}
}
