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

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import java.util.ArrayList;
import java.util.Objects;
import java.util.Optional;

/**
 * Restricts the image of a wrapped relation to the states of a {@code constraint} set, descending
 * the constraint node in lockstep with the relation. Used for constrained saturation (CTL EU).
 *
 * <p>RELATION-DRIVEN: enumeration cursors the wrapped relation's views and probes the constraint by
 * key. Use this variant when the relation is explicit and cheap to enumerate (e.g. the reversed
 * explicit relation in CTL EU). When the relation is symbolic and the constraint is explicit, use
 * {@link ConstraintDrivenAndNextStateDescriptor} instead, or enumeration triggers solver-driven
 * expansion of the symbolic image.
 *
 * <p>The views prune constraint-zero keys by key absence: satFire asserts that off-diagonal values
 * are never {@code terminalEmpty}, and relProd assumes every descended branch reaches a terminal
 * with {@code evaluate() == true}. The constraint is part of equals/hashCode, otherwise distinct
 * constraints collide in the saturation cache.
 */
public final class RelationDrivenAndNextStateDescriptor implements AbstractNextStateDescriptor {

    private final AbstractNextStateDescriptor wrapped;

    private final MddHandle constraint;

    private RelationDrivenAndNextStateDescriptor(
            AbstractNextStateDescriptor wrapped, MddHandle constraint) {
        this.wrapped = wrapped;
        this.constraint = Preconditions.checkNotNull(constraint);
    }

    public static AbstractNextStateDescriptor of(
            AbstractNextStateDescriptor wrapped, MddHandle constraint) {
        if (wrapped == AbstractNextStateDescriptor.terminalEmpty() || constraint.isTerminalZero()) {
            return AbstractNextStateDescriptor.terminalEmpty();
        }
        return new RelationDrivenAndNextStateDescriptor(wrapped, constraint);
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        final IntObjMapView<AbstractNextStateDescriptor> diagonal =
                wrapped.getDiagonal(localStateSpace);
        // A default-only (don't-care) constraint level has an empty explicit key set; trimming to
        // it
        // would silently empty the diagonal and lose transitions. In that case every key maps to
        // the
        // default child (constraint.get(key)), so descend without trimming.
        final IntObjMapView<AbstractNextStateDescriptor> trimmed =
                constraint.keySet().isEmpty() ? diagonal : diagonal.trim(constraint.keySet());
        return new IntObjMapViews.Transforming<>(
                trimmed,
                (descriptor, key) -> {
                    // trim drops the wrapped view's default value; SimpleSaturationProvider
                    // dereferences the diagonal default as the next-level dsat, so map the
                    // resulting null to terminalEmpty (matching MddNodeNextStateDescriptor)
                    if (key == null)
                        return descriptor == null
                                ? AbstractNextStateDescriptor.terminalEmpty()
                                : descriptor;
                    return RelationDrivenAndNextStateDescriptor.of(descriptor, constraint.get(key));
                });
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {
        // the constraint restricts the target (the inner key); the inner view supports only
        // cursor()/get(), so constraint-zero targets are skipped with a cursor instead of trim
        return new IntObjMapViews.Transforming<>(
                wrapped.getOffDiagonal(localStateSpace), this::constrainInner);
    }

    private IntObjMapView<AbstractNextStateDescriptor> constrainInner(
            IntObjMapView<AbstractNextStateDescriptor> inner) {
        return new IntObjMapView<>() {
            @Override
            public IntObjCursor<? extends AbstractNextStateDescriptor> cursor() {
                final IntObjCursor<? extends AbstractNextStateDescriptor> c = inner.cursor();
                return new IntObjCursor<>() {
                    @Override
                    public int key() {
                        return c.key();
                    }

                    @Override
                    public AbstractNextStateDescriptor value() {
                        return RelationDrivenAndNextStateDescriptor.of(
                                c.value(), constraint.get(c.key()));
                    }

                    @Override
                    public boolean moveNext() {
                        while (c.moveNext()) {
                            if (!constraint.get(c.key()).isTerminalZero()) return true;
                        }
                        return false;
                    }
                };
            }

            @Override
            public AbstractNextStateDescriptor get(int key) {
                final MddHandle childConstraint = constraint.get(key);
                if (childConstraint.isTerminalZero())
                    return AbstractNextStateDescriptor.terminalEmpty();
                return RelationDrivenAndNextStateDescriptor.of(inner.get(key), childConstraint);
            }

            @Override
            public boolean isEmpty() {
                throw new UnsupportedOperationException();
            }

            @Override
            public boolean isProcedural() {
                throw new UnsupportedOperationException();
            }

            @Override
            public boolean containsKey(int key) {
                throw new UnsupportedOperationException();
            }

            @Override
            public AbstractNextStateDescriptor defaultValue() {
                throw new UnsupportedOperationException();
            }

            @Override
            public int size() {
                throw new UnsupportedOperationException();
            }
        };
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        return wrapped.split()
                .map(
                        iterable -> {
                            var list = new ArrayList<AbstractNextStateDescriptor>();
                            iterable.forEach(
                                    it ->
                                            list.add(
                                                    new RelationDrivenAndNextStateDescriptor(
                                                            it, constraint)));
                            return list;
                        });
    }

    @Override
    public boolean isLocallyIdentity(StateSpaceInfo stateSpaceInfo) {
        return wrapped.isLocallyIdentity(stateSpaceInfo);
    }

    @Override
    public boolean evaluate() {
        return wrapped.evaluate() && !constraint.isTerminalZero();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        RelationDrivenAndNextStateDescriptor that = (RelationDrivenAndNextStateDescriptor) o;
        return Objects.equals(wrapped, that.wrapped) && Objects.equals(constraint, that.constraint);
    }

    @Override
    public int hashCode() {
        return Objects.hash(wrapped, constraint);
    }

    @Override
    public String toString() {
        return "AndByRelation(" + wrapped + ", " + constraint + ")";
    }
}
