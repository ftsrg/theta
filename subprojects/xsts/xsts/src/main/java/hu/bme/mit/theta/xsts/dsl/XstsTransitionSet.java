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
package hu.bme.mit.theta.xsts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.DynamicScope;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.TransitionSetContext;
import java.util.List;

public class XstsTransitionSet {

    private final DynamicScope scope;
    private final SymbolTable typeTable;
    private final TransitionSetContext context;

    public XstsTransitionSet(
            final DynamicScope scope,
            final SymbolTable typeTable,
            final TransitionSetContext context) {
        this.scope = checkNotNull(scope);
        this.typeTable = checkNotNull(typeTable);
        this.context = checkNotNull(context);
    }

    public NonDetStmt instantiate(final Env env) {
        final TransitionSetCreatorVisitor visitor = new TransitionSetCreatorVisitor(env);
        final NonDetStmt stmt = context.accept(visitor);
        if (stmt == null) {
            throw new AssertionError();
        } else {
            return stmt;
        }
    }

    private final class TransitionSetCreatorVisitor extends XstsDslBaseVisitor<NonDetStmt> {

        private final Env env;

        public TransitionSetCreatorVisitor(final Env env) {
            this.env = checkNotNull(env);
        }

        @Override
        public NonDetStmt visitTransitionSet(TransitionSetContext ctx) {
            final List<Stmt> stmts =
                    ctx.stmts.stream()
                            .map(
                                    (stmtContext ->
                                            new XstsStatement(scope, typeTable, stmtContext)
                                                    .instantiate(env)))
                            .toList();
            return NonDetStmt.of(stmts);
        }
    }
}
