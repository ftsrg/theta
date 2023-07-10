/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.dsl.DynamicScope;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.TransitionSetContext;
import hu.bme.mit.theta.xsts.type.XstsType;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class XstsTransitionSet {

    private final DynamicScope scope;
    private final SymbolTable typeTable;
    private final TransitionSetContext context;
    private final Map<VarDecl<?>, XstsType<?>> varToType;

    public XstsTransitionSet(final DynamicScope scope, final SymbolTable typeTable,
                             final TransitionSetContext context, final Map<VarDecl<?>, XstsType<?>> varToType) {
        this.scope = checkNotNull(scope);
        this.typeTable = checkNotNull(typeTable);
        this.context = checkNotNull(context);
        this.varToType = checkNotNull(varToType);
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
            final List<Stmt> stmts = ctx.stmts.stream()
                    .map((stmtContext -> new XstsStatement(scope, typeTable, stmtContext,
                            varToType).instantiate(env))).collect(Collectors.toList());
            return NonDetStmt.of(stmts);
        }
    }

}
