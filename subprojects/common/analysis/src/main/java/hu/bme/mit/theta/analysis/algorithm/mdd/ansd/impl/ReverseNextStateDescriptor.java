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

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.*;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariableHandle;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Optional;

public class ReverseNextStateDescriptor implements AbstractNextStateDescriptor {

    private final MddHandle stateSpace;

    private final MddNode transitions;

    private final MddVariableHandle variableHandle;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ReverseNextStateDescriptor that = (ReverseNextStateDescriptor) o;
        return Objects.equals(stateSpace, that.stateSpace)
                && Objects.equals(transitions, that.transitions)
                && Objects.equals(variableHandle, that.variableHandle);
    }

    @Override
    public int hashCode() {
        return Objects.hash(stateSpace, transitions, variableHandle);
    }

    private ReverseNextStateDescriptor(MddHandle stateSpace, MddNode transitions, MddVariableHandle variableHandle) {
        this.stateSpace = stateSpace;
        this.transitions = transitions;
        this.variableHandle = Preconditions.checkNotNull(variableHandle);
        Preconditions.checkArgument(
                (variableHandle.isTerminal() && transitions.isTerminal() && stateSpace.isTerminal())
                        || transitions.isOn(variableHandle.getVariable().orElseThrow()));
    }

    private static AbstractNextStateDescriptor of(MddHandle stateSpace, MddNode transitions, MddVariableHandle variableHandle) {
        return (transitions == null || transitions == variableHandle.getMddGraph().getTerminalZeroNode() || stateSpace.isTerminalZero())
                ? AbstractNextStateDescriptor.terminalEmpty()
                : new ReverseNextStateDescriptor(stateSpace, transitions, variableHandle);
    }

//    public static AbstractNextStateDescriptor of(MddHandle handle) {
//        return of(handle.getNode(), handle.getVariableHandle());
//    }

    @Override
    public boolean evaluate() {
        return true;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        // easy: its the same
        return null;
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {

//        stateSpace.keySet().intersect(
//                new IntSetView.AbstractIntSetView() {
//                    @Override
//                    public boolean contains(int i) {
//                        return ;
//                    }
//
//                    @Override
//                    public IntCursor cursor() {
//                        return null;
//                    }
//
//                    @Override
//                    public boolean isEmpty() {
//                        return false;
//                    }
//
//                    @Override
//                    public boolean isProcedural() {
//                        return false;
//                    }
//
//                    @Override
//                    public int size() {
//                        return 0;
//                    }
//                }
//        )

//        return new IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>>() {
//            @Override
//            public boolean isEmpty() {
//                // diagonal is empty if edge is not test or never enabled
//                return takes == puts || takes >= inhibits;
//            }
//
//            @Override
//            public boolean isProcedural() {
//                return true;
//            }
//
//            @Override
//            public boolean containsKey(final int key) {
//
//                for (var cursor = stateSpace.keySet().cursor(); cursor.moveNext();){
//
//                }
//            }
//
//            @Override
//            public IntObjMapView<AbstractNextStateDescriptor> get(final int from) {
//                if (containsKey(from)) {
//                    return new IntObjMapView<AbstractNextStateDescriptor>() {
//                        @Override
//                        public boolean isEmpty() {
//                            return false;
//                        }
//
//                        @Override
//                        public boolean isProcedural() {
//                            return false;
//                        }
//
//                        @Override
//                        public boolean containsKey(final int to) {
//                            return to == from - takes + puts;
//                        }
//
//                        @Override
//                        public AbstractNextStateDescriptor get(final int to) {
//                            if (containsKey(to)) {
//                                return continuation;
//                            } else {
//                                return defaultValue();
//                            }
//                        }
//
//                        @Override
//                        public AbstractNextStateDescriptor defaultValue() {
//                            return AbstractNextStateDescriptor.terminalEmpty();
//                        }
//
//                        @Override
//                        public IntObjCursor<? extends AbstractNextStateDescriptor> cursor() {
//                            return new IntObjCursor<AbstractNextStateDescriptor>() {
//                                int current = from - takes + puts - 1;
//
//                                @Override
//                                public int key() {
//                                    if (!containsKey(current)) {
//                                        throw new NoSuchElementException();
//                                    }
//                                    return current;
//                                }
//
//                                @Override
//                                public AbstractNextStateDescriptor value() {
//                                    if (!containsKey(current)) {
//                                        throw new NoSuchElementException();
//                                    }
//                                    return continuation;
//                                }
//
//                                @Override
//                                public boolean moveNext() {
//                                    return ++current <= from - takes + puts;
//                                }
//                            };
//                        }
//
//                        @Override
//                        public int size() {
//                            return 1;
//                        }
//                    };
//                } else {
//                    return defaultValue();
//                }
//            }
//
//            @Override
//            public IntObjMapView<AbstractNextStateDescriptor> defaultValue() {
//                return IntObjMapView.empty();
//            }
//
//            @Override
//            public IntObjCursor<? extends IntObjMapView<AbstractNextStateDescriptor>> cursor() {
//                return new IntObjCursor<IntObjMapView<AbstractNextStateDescriptor>>() {
//                    int current = takes - 1;
//
//                    @Override
//                    public int key() {
//                        if (!containsKey(current)) {
//                            throw new NoSuchElementException();
//                        }
//                        return current;
//                    }
//
//                    @Override
//                    public IntObjMapView<AbstractNextStateDescriptor> value() {
//                        if (!containsKey(current)) {
//                            throw new NoSuchElementException();
//                        }
//                        return get(current);
//                    }
//
//                    @Override
//                    public boolean moveNext() {
//                        return ++current < inhibits;
//                    }
//                };
//            }
//
//            @Override
//            public int size() {
//                return (inhibits == Integer.MAX_VALUE) ? -1 : inhibits - takes;
//            }
//        };
        return null;
    }
}
