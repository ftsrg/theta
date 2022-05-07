/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis.impl.multithread;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

public class XcfaProcessState<S extends ExprState> implements ExprState {
    private final S state;
    private final XcfaLocation location;

    public XcfaProcessState(final S state, final XcfaLocation location) {
        this.state = state;
        this.location = location;
    }

    @Override
    public boolean isBottom() {
        return state.isBottom();
    }

    @Override
    public Expr<BoolType> toExpr() {
        return state.toExpr();
    }

    public S getState() {
        return state;
    }

    public XcfaLocation getLocation() {
        return location;
    }
}
