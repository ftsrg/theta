/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class ItpZoneState implements ExprState {

    private final ZoneState concrState;
    private final ZoneState abstrState;

    private static final int HASH_SEED = 3361;
    private volatile int hashCode = 0;

    private ItpZoneState(final ZoneState concrState, final ZoneState abstrState) {
        this.concrState = checkNotNull(concrState);
        this.abstrState = checkNotNull(abstrState);
        assert concrState.isLeq(abstrState);
    }

    public static ItpZoneState of(final ZoneState state, final ZoneState interpolant) {
        return new ItpZoneState(state, interpolant);
    }

    ////

    public ZoneState getConcrState() {
        return concrState;
    }

    public ZoneState getAbstrState() {
        return abstrState;
    }

    ////

    public boolean isLeq(final ItpZoneState that) {
        return this.abstrState.isLeq(that.abstrState);
    }

    ////

    public ItpZoneState withConcrState(final ZoneState concrState) {
        return ItpZoneState.of(concrState, abstrState);
    }

    public ItpZoneState withAbstrState(final ZoneState abstrState) {
        return ItpZoneState.of(concrState, abstrState);
    }

    ////

    @Override
    public boolean isBottom() {
        return concrState.isBottom();
    }

    @Override
    public Expr<BoolType> toExpr() {
        if (isBottom()) {
            return False();
        } else {
            return abstrState.toExpr();
        }
    }

    ////

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 37 * result + concrState.hashCode();
            result = 37 * result + abstrState.hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final ItpZoneState that = (ItpZoneState) obj;
            return this.concrState.equals(that.concrState)
                    && this.abstrState.equals(that.abstrState);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName())
                .body()
                .add(concrState)
                .add(abstrState)
                .toString();
    }
}
