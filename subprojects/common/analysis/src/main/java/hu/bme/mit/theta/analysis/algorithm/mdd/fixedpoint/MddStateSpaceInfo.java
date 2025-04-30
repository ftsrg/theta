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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.ObjIntMap;
import com.koloboke.collect.map.hash.HashObjIntMaps;
import com.koloboke.collect.set.ObjSet;
import com.koloboke.collect.set.hash.HashObjSets;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.collections.IntStatistics;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

public final class MddStateSpaceInfo implements StateSpaceInfo {
    private final MddVariable variable;
    private final MddNode mddNode;

    private static BinaryOperationCache<MddVariable, MddNode, MddNode> cache =
            new BinaryOperationCache<>();
    private MddNode structuralRepresentation = null;

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
    public MddNode toStructuralRepresentation() {
        if (structuralRepresentation == null) {
            var cached = cache.getOrNull(variable, mddNode);
            if (cached != null) {
                structuralRepresentation = cached;
                return structuralRepresentation;
            }
            final BoundsCollector boundsCollector = new BoundsCollector(mddNode, variable);
            structuralRepresentation = representBounds(variable, boundsCollector);
            cache.addToCache(variable, mddNode, structuralRepresentation);
        }
        return structuralRepresentation;
    }

    private MddNode representBounds(MddVariable variable, BoundsCollector boundsCollector) {
        final MddNode continuation;
        if (variable.getLower().isPresent()) {
            continuation = representBounds(variable.getLower().get(), boundsCollector);
        } else {
            final MddGraph<Expr<BoolType>> mddGraph =
                    (MddGraph<Expr<BoolType>>) variable.getMddGraph();
            continuation = mddGraph.getNodeFor(True());
        }
        final var bounds = boundsCollector.getBoundsFor(variable);
        final IntObjMapView<MddNode> template;
        if (bounds.isPresent()) {
            if (Objects.equals(bounds.get().first, bounds.get().second)) {
                template = IntObjMapView.singleton(bounds.get().first, continuation);
            } else {
                // TODO: canonization of trimmed intobjmapviews could be improved
                template =
                        new IntObjMapViews.Trimmed<>(
                                IntObjMapView.empty(continuation),
                                IntSetView.range(bounds.get().first, bounds.get().second + 1));
            }
        } else {
            template = IntObjMapView.empty(continuation);
        }

        return variable.checkInNode(MddStructuralTemplate.of(template));
    }

    //    private MddNode collapseEdges(MddNode parent) {
    //
    //        IntSetView setView = IntSetView.empty();
    //        for (var c = parent.cursor(); c.moveNext(); ) {
    //            setView = setView.union(c.value().keySet());
    //        }
    //
    //    }

    private static class BoundsCollector {

        private final ObjIntMap<MddVariable> lowerBounds;
        private final ObjIntMap<MddVariable> upperBounds;
        private final ObjSet<MddVariable> hasDefaultValue;

        public BoundsCollector(MddNode rootNode, MddVariable variable) {
            Preconditions.checkNotNull(rootNode);
            this.lowerBounds = HashObjIntMaps.newUpdatableMap();
            this.upperBounds = HashObjIntMaps.newUpdatableMap();
            this.hasDefaultValue = HashObjSets.newUpdatableSet();

            final Set<MddNode> traversed = Containers.createSet();
            traverse(rootNode, variable, traversed);
        }

        private void traverse(
                final MddNode node, final MddVariable variable, final Set<MddNode> traversed) {
            if (traversed.contains(node) || node.isTerminal()) {
                return;
            } else {
                traversed.add(node);
            }
            Preconditions.checkNotNull(variable);

            for (var c = node.cursor(); c.moveNext(); ) {} // TODO delete later

            final var nodeInterpreter = variable.getNodeInterpreter(node);
            if (nodeInterpreter.defaultValue() != null) {
                final MddNode defaultValue = nodeInterpreter.defaultValue();
                traverse(defaultValue, variable.getLower().orElse(null), traversed);
                hasDefaultValue.add(variable);
            } else {
                final IntStatistics statistics = nodeInterpreter.statistics();
                lowerBounds.put(
                        variable,
                        Math.min(
                                lowerBounds.getOrDefault(variable, Integer.MAX_VALUE),
                                statistics.lowestValue()));
                upperBounds.put(
                        variable,
                        Math.max(
                                upperBounds.getOrDefault(variable, Integer.MIN_VALUE),
                                statistics.highestValue()));

                for (var cur = nodeInterpreter.cursor(); cur.moveNext(); ) {
                    if (cur.value() != null) {
                        traverse(cur.value(), variable.getLower().orElse(null), traversed);
                    }
                }
            }
        }

        public Optional<Pair<Integer, Integer>> getBoundsFor(MddVariable variable) {
            if (hasDefaultValue.contains(variable)) return Optional.empty();
            if (!lowerBounds.containsKey(variable) || !upperBounds.containsKey(variable))
                return Optional.empty();
            return Optional.of(
                    new Pair<>(lowerBounds.getInt(variable), upperBounds.getInt(variable)));
        }
    }
}
