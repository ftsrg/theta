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

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Collection;
import java.util.stream.Collectors;

public final class XstsLts<S extends ExprState> implements LTS<XstsState<S>, XstsAction> {

    private final NonDetStmt trans;
    private final NonDetStmt env;
    private final NonDetStmt init;

    private final XstsStmtOptimizer<S> stmtOptimizer;

    private XstsLts(final XSTS xsts, final XstsStmtOptimizer<S> stmtOptimizer) {
        trans = xsts.getTran();
        env = xsts.getEnv();
        init = xsts.getInit();

        this.stmtOptimizer = stmtOptimizer;
    }

    public static <S extends ExprState> LTS<XstsState<S>, XstsAction> create(final XSTS xsts,
                                                                             final XstsStmtOptimizer<S> stmtOptimizer) {
        return new XstsLts<>(xsts, stmtOptimizer);
    }

    @Override
    public Collection<XstsAction> getEnabledActionsFor(XstsState<S> state) {
        NonDetStmt enabledSet;
        if (!state.isInitialized()) {
            enabledSet = init;
        } else if (state.lastActionWasEnv()) {
            enabledSet = trans;
        } else {
            enabledSet = env;
        }

        return enabledSet.getStmts().stream()
                .map(stmt -> stmtOptimizer.optimizeStmt(state, stmt))
                .map(XstsAction::create)
                .collect(Collectors.toList());
    }
}
