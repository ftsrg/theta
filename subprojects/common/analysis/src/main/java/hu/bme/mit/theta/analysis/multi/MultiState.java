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
package hu.bme.mit.theta.analysis.multi;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Objects;
import hu.bme.mit.theta.analysis.State;

@SuppressWarnings("java:S119")
public abstract class MultiState<
                LState extends State, RState extends State, DataState extends State>
        implements State {

    private final LState leftState;
    private final RState rightState;
    private final DataState dataState;

    /**
     * Shows if this state derived from an action that considered the left or the right state of the
     * previous multi state. Can and will be null if this is an initial state.
     */
    private final MultiSide sourceSide;

    /**
     * Flag whether to include {@link hu.bme.mit.theta.analysis.multi.MultiState#sourceSide} in
     * {@link hu.bme.mit.theta.analysis.multi.MultiState#equals(Object)}
     */
    private final boolean sourceMattersInEquality;

    protected MultiState(
            LState ls,
            RState rs,
            DataState data,
            MultiSide sourceSide,
            boolean sourceMattersInEquality) {
        checkArgument(sourceSide != MultiSide.BOTH);
        leftState = ls;
        rightState = rs;
        dataState = data;
        this.sourceSide = sourceSide;
        this.sourceMattersInEquality = sourceMattersInEquality;
    }

    public MultiSide getSourceSide() {
        return sourceSide;
    }

    @Override
    public boolean isBottom() {
        return dataState.isBottom() || leftState.isBottom() || rightState.isBottom();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        MultiState<?, ?, ?> that = (MultiState<?, ?, ?>) o;
        if ((sourceMattersInEquality || that.sourceMattersInEquality)
                && sourceSide != that.sourceSide) {
            return false;
        }
        return Objects.equal(leftState, that.leftState)
                && Objects.equal(rightState, that.rightState)
                && Objects.equal(dataState, that.dataState);
    }

    @Override
    public int hashCode() {
        if (sourceMattersInEquality)
            return Objects.hashCode(leftState, rightState, dataState, sourceSide);
        return Objects.hashCode(leftState, rightState, dataState);
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

    public boolean isSourceMatteringInEquality() {
        return sourceMattersInEquality;
    }

    @Override
    public String toString() {
        return "MultiState{"
                + "leftState="
                + leftState
                + ", rightState="
                + rightState
                + ", dataState="
                + dataState
                + '}';
    }
}
