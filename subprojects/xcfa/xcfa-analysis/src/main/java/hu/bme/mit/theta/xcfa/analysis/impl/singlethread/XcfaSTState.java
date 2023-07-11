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
package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.passes.processpass.FunctionInlining;

public abstract class XcfaSTState<S extends ExprState> extends XcfaState<S> {

    protected final S globalState;

    protected XcfaSTState(final S globalState) {
        this.globalState = globalState;
    }

    public static <S extends ExprState> XcfaSTState<S> create(final XcfaLocation currentLoc,
                                                              final S globalState) {
        return FunctionInlining.inlining == FunctionInlining.InlineFunctions.ON ?
                new XcfaSTStateSimple<>(currentLoc, globalState) :
                new XcfaSTStateStack<>(currentLoc, globalState);
    }

    @Override
    public boolean isBottom() {
        return globalState.isBottom();
    }

    @Override
    public Expr<BoolType> toExpr() {
        return globalState.toExpr();
    }

    @Override
    public S getGlobalState() {
        return globalState;
    }

    @Override
    public abstract XcfaLocation getCurrentLoc();

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        XcfaSTState<?> that = (XcfaSTState<?>) o;
        return globalState.equals(that.globalState) && equalLocations(that);
    }

    public abstract boolean equalLocations(XcfaSTState<?> o);

    public abstract XcfaSTState<S> withState(final S succState);

    public abstract XcfaSTState<S> withLocation(final XcfaLocation location);
}
