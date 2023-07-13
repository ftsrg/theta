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

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class BasicExprMeetStrategy implements ExprLattice.MeetStrategy {

    private static final BasicExprMeetStrategy INSTANCE = new BasicExprMeetStrategy();

    private BasicExprMeetStrategy() {
    }

    public static BasicExprMeetStrategy getInstance() {
        return INSTANCE;
    }

    @Override
    public BasicExprState meet(final BasicExprState state1, final BasicExprState state2) {
        final Expr<BoolType> andExpr = And(state1.toExpr(), state2.toExpr());
        return BasicExprState.of(andExpr);
    }
}
