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
package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.stmt.Stmt;

public class Prod2ExplPredStmtOptimizer implements StmtOptimizer<Prod2State<ExplState, PredState>> {

    private final StmtOptimizer<ExplState> stmtOptimizer;

    private Prod2ExplPredStmtOptimizer(final StmtOptimizer<ExplState> stmtOptimizer) {
        this.stmtOptimizer = stmtOptimizer;
    }

    public static Prod2ExplPredStmtOptimizer create(final StmtOptimizer<ExplState> stmtOptimizer) {
        return new Prod2ExplPredStmtOptimizer(stmtOptimizer);
    }

    @Override
    public Stmt optimizeStmt(Prod2State<ExplState, PredState> state, Stmt stmt) {
        return stmtOptimizer.optimizeStmt(state.getState1(), stmt);
    }
}
