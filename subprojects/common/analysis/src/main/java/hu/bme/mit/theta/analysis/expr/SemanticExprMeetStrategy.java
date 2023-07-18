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

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.solver.Solver;

import static com.google.common.base.Preconditions.checkNotNull;

public final class SemanticExprMeetStrategy implements ExprLattice.MeetStrategy {

    private final PartialOrd<ExprState> partialOrd;
    private final BasicExprMeetStrategy basicMeetStrategy;

    private SemanticExprMeetStrategy(final Solver solver) {
        checkNotNull(solver);
        partialOrd = ExprOrd.create(solver);
        basicMeetStrategy = BasicExprMeetStrategy.getInstance();
    }

    public static SemanticExprMeetStrategy create(final Solver solver) {
        return new SemanticExprMeetStrategy(solver);
    }

    @Override
    public BasicExprState meet(final BasicExprState state1, final BasicExprState state2) {
        if (partialOrd.isLeq(state1, state2)) {
            return state1;
        }
        if (partialOrd.isLeq(state2, state1)) {
            return state2;
        }
        return basicMeetStrategy.meet(state1, state2);
    }
}
