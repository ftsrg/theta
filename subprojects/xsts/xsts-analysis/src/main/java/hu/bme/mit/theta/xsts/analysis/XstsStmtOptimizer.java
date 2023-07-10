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
package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.stmt.Stmt;

public class XstsStmtOptimizer<S extends ExprState> implements StmtOptimizer<XstsState<S>> {

    private final StmtOptimizer<S> stmtOptimizer;

    private XstsStmtOptimizer(final StmtOptimizer<S> stmtOptimizer) {
        this.stmtOptimizer = stmtOptimizer;
    }

    public static <S extends ExprState> XstsStmtOptimizer<S> create(
            final StmtOptimizer<S> stmtOptimizer) {
        return new XstsStmtOptimizer<>(stmtOptimizer);
    }

    @Override
    public Stmt optimizeStmt(final XstsState<S> state, final Stmt stmt) {
        return stmtOptimizer.optimizeStmt(state.getState(), stmt);
    }
}
