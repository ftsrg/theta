/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import java.util.Objects;
import java.util.Optional;

/**
 * Presents {@code aligned} — a constraint or bound built in a shorter variable order — at a taller
 * order by lifting it over a don't-care prefix: above {@code alignTraceInfo} every variable is
 * unconstrained (a default edge into the same lift), and at that level it delegates to {@code
 * aligned}, keeping {@link AndNextStateDescriptor} a pure aligned intersection. A {@link
 * AbstractNextStateDescriptor.Postcondition} operand lifts as a Postcondition, a full relation as a
 * full relation.
 */
public sealed class LiftNextStateDescriptor implements AbstractNextStateDescriptor
        permits LiftNextStateDescriptor.LiftPostcondition {

    final AbstractNextStateDescriptor aligned;
    final Object alignTraceInfo;

    private LiftNextStateDescriptor(AbstractNextStateDescriptor aligned, Object alignTraceInfo) {
        this.aligned = aligned;
        this.alignTraceInfo = alignTraceInfo;
    }

    public static AbstractNextStateDescriptor of(
            AbstractNextStateDescriptor aligned, Object alignTraceInfo) {
        if (aligned == AbstractNextStateDescriptor.terminalEmpty()) return aligned;
        if (aligned instanceof AbstractNextStateDescriptor.Postcondition post) {
            return new LiftPostcondition(post, alignTraceInfo);
        }
        return new LiftNextStateDescriptor(aligned, alignTraceInfo);
    }

    final boolean atAlignedLevel(StateSpaceInfo localStateSpace) {
        return Objects.equals(localStateSpace.getTraceInfo(), alignTraceInfo);
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        if (atAlignedLevel(localStateSpace)) return aligned.getDiagonal(localStateSpace);
        // don't-care prefix level: every key continues unconstrained one level down
        return IntObjMapView.empty(this);
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {
        if (atAlignedLevel(localStateSpace)) return aligned.getOffDiagonal(localStateSpace);
        return IntObjMapView.empty(IntObjMapView.empty(this));
    }

    @Override
    public boolean isSourceStateDefined() {
        return aligned.isSourceStateDefined();
    }

    @Override
    public boolean isNextStateDefined() {
        return aligned.isNextStateDefined();
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        return Optional.empty();
    }

    @Override
    public boolean isLocallyIdentity(StateSpaceInfo localStateSpace) {
        // a don't-care prefix level constrains nothing (locally identity); the operand decides once
        // aligned
        return !atAlignedLevel(localStateSpace) || aligned.isLocallyIdentity(localStateSpace);
    }

    @Override
    public boolean evaluate() {
        return aligned.evaluate();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        LiftNextStateDescriptor that = (LiftNextStateDescriptor) o;
        return Objects.equals(aligned, that.aligned)
                && Objects.equals(alignTraceInfo, that.alignTraceInfo);
    }

    @Override
    public int hashCode() {
        return Objects.hash(aligned, alignTraceInfo);
    }

    @Override
    public String toString() {
        return "Lift(" + aligned + " @ " + alignTraceInfo + ")";
    }

    /** A {@link AbstractNextStateDescriptor.Postcondition} operand keeps its target-only shape. */
    static final class LiftPostcondition extends LiftNextStateDescriptor
            implements AbstractNextStateDescriptor.Postcondition {

        private LiftPostcondition(
                AbstractNextStateDescriptor.Postcondition aligned, Object alignTraceInfo) {
            super(aligned, alignTraceInfo);
        }

        @Override
        public IntObjMapView<AbstractNextStateDescriptor> getValuations(
                StateSpaceInfo localStateSpace) {
            if (atAlignedLevel(localStateSpace)) {
                return ((AbstractNextStateDescriptor.Postcondition) aligned)
                        .getValuations(localStateSpace);
            }
            return IntObjMapView.empty(this);
        }

        @Override
        public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo lss) {
            return getValuations(lss);
        }

        @Override
        public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
                StateSpaceInfo lss) {
            return IntObjMapView.empty(getValuations(lss));
        }

        @Override
        public boolean isSourceStateDefined() {
            return false;
        }
    }
}
