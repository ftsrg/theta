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
package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.core.utils.StmtSimplifier;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.Stmt;

public class PredStmtOptimizer implements StmtOptimizer<PredState> {

    private PredStmtOptimizer() {
    }

    private static class LazyHolder {

        static final PredStmtOptimizer INSTANCE = new PredStmtOptimizer();
    }

    public static PredStmtOptimizer getInstance() {
        return PredStmtOptimizer.LazyHolder.INSTANCE;
    }

    @Override
    public Stmt optimizeStmt(final PredState state, final Stmt stmt) {
        return StmtSimplifier.simplifyStmt(ImmutableValuation.empty(), stmt);
    }
}
