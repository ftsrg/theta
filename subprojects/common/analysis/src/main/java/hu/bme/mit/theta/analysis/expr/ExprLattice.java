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
package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public final class ExprLattice implements Lattice<BasicExprState> {

    @FunctionalInterface
    public interface MeetStrategy {
        BasicExprState meet(final BasicExprState state1, final BasicExprState state2);
    }

    private final PartialOrd<ExprState> partialOrd;
    private final MeetStrategy meetStrategy;

    private ExprLattice(final Solver solver, final MeetStrategy meetStrategy) {
        checkNotNull(solver);
        partialOrd = ExprOrd.create(solver);
        this.meetStrategy = checkNotNull(meetStrategy);
    }

    public static ExprLattice create(final Solver solver) {
        return new ExprLattice(solver, BasicExprMeetStrategy.getInstance());
    }

    public static ExprLattice create(final Solver solver, final MeetStrategy meetStrategy) {
        return new ExprLattice(solver, meetStrategy);
    }

    @Override
    public BasicExprState top() {
        return BasicExprState.of(True());
    }

    @Override
    public BasicExprState bottom() {
        return BasicExprState.of(False());
    }

    @Override
    public BasicExprState meet(BasicExprState state1, BasicExprState state2) {
        return meetStrategy.meet(state1, state2);
    }

    @Override
    public BasicExprState join(BasicExprState state1, BasicExprState state2) {
        final Expr<BoolType> orExpr = Or(state1.toExpr(), state2.toExpr());
        return BasicExprState.of(orExpr);
    }

    @Override
    public boolean isLeq(BasicExprState state1, BasicExprState state2) {
        return partialOrd.isLeq(state1, state2);
    }
}
