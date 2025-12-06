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
package hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.ObjObjMap;
import com.koloboke.collect.map.hash.HashObjObjMaps;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.collections.IntStatistics;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.BinaryOperationCache;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;

import java.util.ArrayList;
import java.util.List;

public final class MddStateSpaceInfo implements StateSpaceInfo {
    private final MddVariable variable;
    private final MddNode mddNode;

    private static BinaryOperationCache<MddVariable, MddNode, RecursiveIntObjMapView<?>> cache =
            new BinaryOperationCache<>();
    private RecursiveIntObjMapView<?> structuralRepresentation = null;

    public MddStateSpaceInfo(final MddVariable variable, final MddNode mddNode) {
        this.variable = variable;
        this.mddNode = mddNode;

        for (var c = mddNode.cursor(); c.moveNext(); ) {} // TODO delete later
    }

    @Override
    public Object getTraceInfo() {
        return variable.getTraceInfo();
    }

    // @Override
    // public ElementChain<Object> getComponentChain() {
    // 	class TraceInfoChain implements ElementChain<Object> {
    // 		private final MddVariableHandle mddVariableHandle;
    //
    // 		TraceInfoChain(MddVariableHandle mddVariableHandle) {
    // 			Preconditions.checkArgument(mddVariableHandle.getVariable().isPresent());
    // 			this.mddVariableHandle = mddVariableHandle;
    // 		}
    //
    // 		@Override
    // 		public Object getElement() {
    // 			return mddVariableHandle.getVariable().orElseThrow(AssertionError::new).getTraceInfo();
    // 		}
    //
    // 		@Override
    // 		public ElementChain<Object> next() {
    // 			if (mddVariableHandle.getLower().isPresent()) {
    // 				return new TraceInfoChain(mddVariableHandle.getLower().orElseThrow(AssertionError::new));
    // 			} else {
    // 				return null;
    // 			}
    // 		}
    // 	}
    //
    // 	return new TraceInfoChain(variableHandle);
    // }

    // TODO: else nodes are problematic, better not use them for now
    @Override
    public boolean hasInfiniteStates() {
        if (mddNode.isTerminal()) {
            return true;
        } else if (mddNode.isBelow(variable)) {
            return true;
        } else {
            return !variable.isNullOrZero(mddNode.defaultValue());
        }
    }

    @Override
    public IntSetView getLocalStateSpace() {
        return mddNode.keySet();
    }

    @Override
    public StateSpaceInfo getLocalStateSpace(final Object someLowerComponent) {
        // TODO: Auto-generated method stub.
        throw new UnsupportedOperationException("Not (yet) implemented.");
        // return null;
    }

    @Override
    public RecursiveIntObjMapView<?> toStructuralRepresentation() {
        if (structuralRepresentation == null) {
            var cached = cache.getOrNull(variable, mddNode);
            if (cached != null) {
                structuralRepresentation = cached;
                return structuralRepresentation;
            }
            final BoundsCollector boundsCollector = new BoundsCollector(mddNode, variable);
            structuralRepresentation = representBounds(variable, boundsCollector.bounds);
            cache.addToCache(variable, mddNode, structuralRepresentation);
        }
        return structuralRepresentation;
    }

    private RecursiveIntObjMapView<?> representBounds(final MddVariable variable, final ObjObjMap<MddVariable, BoundsCollector.Bounds> bounds) {
        final RecursiveIntObjMapView<?> continuation;
        if (variable.getLower().isPresent()) {
            continuation = representBounds(variable.getLower().orElseThrow(), bounds);
        } else {
            continuation = RecursiveIntObjMapView.of((IntObjMapView) IntObjMapView.empty());
        }

        final var triple = bounds.get(variable);
        final IntObjMapView<RecursiveIntObjMapView<?>> mapView;
        if (!triple.hasDefault) {
            if (triple.lower == triple.upper) {
                mapView = IntObjMapView.singleton(triple.lower, continuation);
            } else {
                // TODO: canonization of trimmed intobjmapviews could be improved
                mapView = new IntObjMapViews.Trimmed<>(
                    IntObjMapView.empty(continuation),
                    IntSetView.range(triple.lower, triple.upper + 1)
                );
            }
        } else {
            mapView = IntObjMapView.empty(continuation);
        }
        return RecursiveIntObjMapView.of((IntObjMapView) mapView);
    }

    private static class BoundsCollector {

        private final ObjObjMap<MddVariable, Bounds> bounds;

        static class Bounds {
            int lower;
            int upper;
            boolean hasDefault;

            Bounds(
                    int lower,
                    int upper,
                    boolean hasDefault) {
                this.lower = lower;
                this.upper = upper;
                this.hasDefault = hasDefault;
            }
        }

        private static BinaryOperationCache<MddNode, MddVariable, ObjObjMap<MddVariable, Bounds>> cache = new BinaryOperationCache<>();

        public BoundsCollector(MddNode rootNode, MddVariable variable) {
            Preconditions.checkNotNull(rootNode);
            this.bounds = traverse(rootNode, variable);
        }

        private ObjObjMap<MddVariable, Bounds> traverse(
                final MddNode node, final MddVariable variable) {
            final var cached = cache.getOrNull(node, variable);
            if (cached != null) {
                return cached;
            }
            if (node.isTerminal()) {
                return HashObjObjMaps.newUpdatableMap();
            }

            Preconditions.checkNotNull(variable);

            for (var c = node.cursor(); c.moveNext(); ) {} // TODO delete later

            final ObjObjMap<MddVariable, Bounds> returnValue = HashObjObjMaps.newUpdatableMap();
            final var currentBounds = new Bounds(Integer.MAX_VALUE, Integer.MIN_VALUE, false);

            final List<ObjObjMap<MddVariable, Bounds>> childBounds = new ArrayList<>();

            final var nodeInterpreter = variable.getNodeInterpreter(node);
            if (nodeInterpreter.defaultValue() != null) {
                final MddNode defaultValue = nodeInterpreter.defaultValue();
                childBounds.add(traverse(defaultValue, variable.getLower().orElse(null)));
                currentBounds.hasDefault = true;
            } else {
                final IntStatistics statistics = nodeInterpreter.statistics();
                currentBounds.lower = statistics.lowestValue();
                currentBounds.upper = statistics.highestValue();

                for (var cur = nodeInterpreter.cursor(); cur.moveNext(); ) {
                    if (cur.value() != null) {
                        childBounds.add(traverse(cur.value(), variable.getLower().orElse(null)));
                    }
                }
            }

            returnValue.put(variable, currentBounds);
            for (final var childBoundMap : childBounds) {
                for (final var entry : childBoundMap.entrySet()) {
                    final MddVariable var = entry.getKey();
                    final Bounds childBoundsForVar = entry.getValue();

                    final Bounds existingBounds = returnValue.getOrDefault(var, null);
                    if (existingBounds == null) {
                        returnValue.put(
                                var,
                                new Bounds(
                                        childBoundsForVar.lower,
                                        childBoundsForVar.upper,
                                        childBoundsForVar.hasDefault));
                    } else {
                        existingBounds.lower =
                                Math.min(existingBounds.lower, childBoundsForVar.lower);
                        existingBounds.upper =
                                Math.max(existingBounds.upper, childBoundsForVar.upper);
                        existingBounds.hasDefault |= childBoundsForVar.hasDefault;
                    }
                }
            }
            cache.addToCache(node, variable, returnValue);
            return returnValue;
        }
    }
}
