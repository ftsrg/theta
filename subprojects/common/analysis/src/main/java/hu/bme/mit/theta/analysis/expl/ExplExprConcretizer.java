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
package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprSimplifier;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.SimplifierLevel;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public final class ExplExprConcretizer implements Concretizer<ExplState, BasicExprState> {

    private final ExprSimplifier simplifier;
    private final Solver solver;

    private ExplExprConcretizer(final Solver solver) {
        this.solver = checkNotNull(solver);
        simplifier = ExprSimplifier.create(SimplifierLevel.FULL);
    }

    public static ExplExprConcretizer create(final Solver solver) {
        return new ExplExprConcretizer(solver);
    }

    @Override
    public BasicExprState concretize(final ExplState state) {
        return BasicExprState.of(state.toExpr());
    }

    @Override
    public boolean proves(final ExplState concrState, final BasicExprState abstrState) {
        final Expr<BoolType> simplifiedExpr = simplifier.simplify(abstrState.toExpr(), concrState);
        if (simplifiedExpr.equals(True())) {
            return true;
        } else if (simplifiedExpr.equals(False())) {
            return false;
        } else {
            try (WithPushPop wpp = new WithPushPop(solver)) {
                solver.add(PathUtils.unfold(simplifiedExpr, 0));
                final SolverStatus solverStatus = solver.check();
                return solverStatus.isSat();
            }
        }
    }

    @Override
    public boolean inconsistentConcrState(final ExplState state) {
        return state.isBottom();
    }
}
