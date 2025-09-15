/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Edge;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.EdgeContext;
import hu.bme.mit.theta.cfa.dsl.gen.CfaDslParser.StmtContext;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

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

    public List<Edge> instantiate(final CFA.Builder cfa, final Env env) {
        final CfaLocationSymbol sourceSymbol = (CfaLocationSymbol) scope.resolve(source).get();
        final CfaLocationSymbol targetSymbol = (CfaLocationSymbol) scope.resolve(target).get();

        final Loc sourceLoc = (Loc) env.eval(sourceSymbol);
        final Loc targetLoc = (Loc) env.eval(targetSymbol);
        final List<Stmt> stmts =
                statements.stream().map(s -> s.instantiate(env)).collect(Collectors.toList());
        if (stmts.isEmpty()) {
            stmts.add(Stmts.Skip());
        }
        final List<Edge> edges = new ArrayList<>(stmts.size());
        final List<Loc> locs = new ArrayList<>(stmts.size() + 1);
        locs.add(sourceLoc);
        for (int i = 0; i < stmts.size() - 1; ++i) {
            locs.add(cfa.createLoc());
        }
        locs.add(targetLoc);

        for (int i = 0; i < stmts.size(); ++i) {
            edges.add(cfa.createEdge(locs.get(i), locs.get(i + 1), stmts.get(i)));
        }

        return edges;
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
