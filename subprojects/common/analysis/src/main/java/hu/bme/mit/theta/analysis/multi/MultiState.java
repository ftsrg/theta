/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.multi;

import com.google.common.base.Objects;
import hu.bme.mit.theta.analysis.State;

public abstract class MultiState<LState extends State, RState extends State, DataState extends State> implements State {

    private final LState leftState;
    private final RState rightState;
    private final DataState dataState;

    /**
     * Denotes whether this state derived from an action that considered the left state of the previous multi state.
     * Can be null. Is always null for initial states.
     */
    private final MultiSourceSide sourceSide;

    /**
     * Flag whether to include {@link hu.bme.mit.theta.analysis.multi.MultiState#sourceSide} in {@link hu.bme.mit.theta.analysis.multi.MultiState#equals(Object)}
     */
    private final boolean sourceMattersInEquality;

    protected MultiState(LState ls, RState rs, DataState data, MultiSourceSide sourceSide, boolean sourceMattersInEquality) {
        leftState = ls;
        rightState = rs;
        dataState = data;
        this.sourceSide = sourceSide;
        this.sourceMattersInEquality = sourceMattersInEquality;
    }

    public MultiSourceSide getSourceSide() {
        return sourceSide;
    }

    @Override
    public boolean isBottom() {
        return dataState.isBottom() || leftState.isBottom() || rightState.isBottom();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        MultiState<?, ?, ?> that = (MultiState<?, ?, ?>) o;
        if ((sourceMattersInEquality || that.sourceMattersInEquality) && sourceSide != that.sourceSide)
            return false;
        return Objects.equal(leftState, that.leftState) && Objects.equal(rightState, that.rightState) && Objects.equal(dataState, that.dataState);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(leftState, rightState, dataState, sourceSide, sourceMattersInEquality);
    }


    public LState getLeftState() {
        return leftState;
    }

    public RState getRightState() {
        return rightState;
    }

    public DataState getDataState() {
        return dataState;
    }

    public boolean getSourceMattersInEquality() {
        return sourceMattersInEquality;
    }

    @Override
    public String toString() {
        return "MultiState{" +
                "leftState=" + leftState +
                ", rightState=" + rightState +
                ", dataState=" + dataState +
                '}';
    }
}
