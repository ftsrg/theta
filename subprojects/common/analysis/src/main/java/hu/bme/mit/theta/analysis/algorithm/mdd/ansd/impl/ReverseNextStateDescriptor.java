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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl;

import hu.bme.mit.delta.collections.*;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation;
import java.util.Objects;

public class ReverseNextStateDescriptor implements AbstractNextStateDescriptor {

    private final MddHandle stateSpace;
    private final MddNode transitions;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ReverseNextStateDescriptor that = (ReverseNextStateDescriptor) o;
        return Objects.equals(transitions, that.transitions)
                && Objects.equals(stateSpace, that.stateSpace);
    }

    @Override
    public int hashCode() {
        return Objects.hash(transitions, stateSpace);
    }

    private ReverseNextStateDescriptor(MddHandle stateSpace, MddNode transitions) {
        this.transitions = transitions;
        this.stateSpace = stateSpace;
    }

    private static AbstractNextStateDescriptor of(MddHandle stateSpace, MddNode transitions) {
        if (transitions == null || stateSpace.isTerminalZero()) {
            return AbstractNextStateDescriptor.terminalEmpty();
        }
        if (transitions.getRepresentation()
                instanceof IdentityRepresentation identityExpressionRepresentation) {
            final var cont = identityExpressionRepresentation.getContinuation();
            return new IdentityReverseNextStateDescriptor(stateSpace, cont);
        }
        return new ReverseNextStateDescriptor(stateSpace, transitions);
    }

    public static AbstractNextStateDescriptor of(MddHandle stateSpace, MddHandle handle) {
        return of(stateSpace, handle.getNode());
    }

    @Override
    public boolean evaluate() {
        return true;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        // easy: its the same
        return new IntObjMapViews.Transforming<>(
                transitions,
                (n, key) -> {
                    if (key == null || n == null)
                        return AbstractNextStateDescriptor.terminalEmpty();
                    else return ReverseNextStateDescriptor.of(stateSpace.get(key), n.get(key));
                });
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {

        return new IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>>() {

            @Override
            public IntObjMapView<AbstractNextStateDescriptor> get(final int from) {

                return new IntObjMapView<AbstractNextStateDescriptor>() {

                    @Override
                    public boolean isEmpty() {
                        throw new UnsupportedOperationException();
                    }

                    @Override
                    public boolean isProcedural() {
                        throw new UnsupportedOperationException();
                    }

                    @Override
                    public boolean containsKey(int i) {
                        throw new UnsupportedOperationException();
                    }

                    @Override
                    public AbstractNextStateDescriptor get(int i) {
                        throw new UnsupportedOperationException();
                    }

                    @Override
                    public AbstractNextStateDescriptor defaultValue() {
                        throw new UnsupportedOperationException();
                    }

                    @Override
                    public IntObjCursor<? extends AbstractNextStateDescriptor> cursor() {
                        return new IntObjCursor<AbstractNextStateDescriptor>() {
                            private final IntObjCursor<? extends MddNode> toValues =
                                    transitions.trim(stateSpace.keySet()).cursor();

                            @Override
                            public int key() {
                                return toValues.key();
                            }

                            @Override
                            public AbstractNextStateDescriptor value() {
                                return ReverseNextStateDescriptor.of(
                                        stateSpace.get(key()), toValues.value().get(from));
                            }

                            @Override
                            public boolean moveNext() {
                                while (toValues.moveNext()) {
                                    if (toValues.value().containsKey(from)) return true;
                                }
                                return false;
                            }
                        };
                    }

                    @Override
                    public int size() {
                        throw new UnsupportedOperationException();
                    }
                };
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
            public boolean containsKey(final int key) {
                throw new UnsupportedOperationException();
            }

            @Override
            public IntObjMapView<AbstractNextStateDescriptor> defaultValue() {
                throw new UnsupportedOperationException();
            }

            @Override
            public IntObjCursor<? extends IntObjMapView<AbstractNextStateDescriptor>> cursor() {
                throw new UnsupportedOperationException();
            }

            @Override
            public int size() {
                throw new UnsupportedOperationException();
            }
        };
    }

    @Override
    public boolean isLocallyIdentity(StateSpaceInfo stateSpaceInfo) {
        return false;
    }

    @Override
    public String toString() {
        return "Reversed " + transitions;
    }

    private static class IdentityReverseNextStateDescriptor implements AbstractNextStateDescriptor {

        private final MddHandle stateSpace;
        private final MddNode transitionsContinuation;

        private IdentityReverseNextStateDescriptor(
                MddHandle stateSpace, MddNode transitionsContinuation) {
            this.stateSpace = stateSpace;
            this.transitionsContinuation = transitionsContinuation;
        }

        @Override
        public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(
                StateSpaceInfo localStateSpace) {
            return new IntObjMapViews.Transforming<>(
                    stateSpace,
                    (n, key) -> {
                        if (key == null || n == null)
                            return AbstractNextStateDescriptor.terminalEmpty();
                        else
                            return ReverseNextStateDescriptor.of(
                                    (MddHandle) n, transitionsContinuation);
                    });
        }

        @Override
        public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
                StateSpaceInfo localStateSpace) {
            return IntObjMapView.empty(
                    IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty()));
        }
    }
}
