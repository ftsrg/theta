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

import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import java.util.function.Consumer;
import java.util.function.ToLongFunction;

public final class CursorRelationalProductProvider implements RelationalProductProvider {
    private final CacheManager<BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
            cacheManager = new CacheManager<>(v -> new BinaryOperationCache<>());
    private final MddVariableOrder variableOrder;

    public CursorRelationalProductProvider(final MddVariableOrder variableOrder) {
        this.variableOrder = variableOrder;
        this.variableOrder.getMddGraph().registerCleanupListener(this);
    }

    private MddNode recurse(
            final MddNode mddNode,
            final AbstractNextStateDescriptor nextState,
            final AbstractNextStateDescriptor.Cursor nextStateCursor,
            MddVariable currentVariable,
            final CacheManager<BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
                            .CacheHolder
                    currentCache) {
        if (currentVariable.getLower().isPresent()) {
            return doCompute(
                    mddNode,
                    nextState,
                    nextStateCursor,
                    currentVariable.getLower().get(),
                    currentCache.getLower());
        } else {
            return computeTerminal(mddNode, nextState, currentVariable.getMddGraph());
        }
    }

    private MddNode unionChildren(
            final MddNode lhs, final MddNode rhs, MddVariable currentVariable) {
        if (currentVariable.getLower().isPresent()) {
            return currentVariable.getLower().get().union(lhs, rhs);
        } else {
            return currentVariable.getMddGraph().unionTerminal(lhs, rhs);
        }
    }

    @Override
    public MddNode compute(
            final MddNode mddNode,
            final AbstractNextStateDescriptor abstractNextStateDescriptor,
            final MddVariable mddVariable) {
        return doCompute(
                mddNode,
                abstractNextStateDescriptor,
                abstractNextStateDescriptor.rootCursor(),
                mddVariable,
                cacheManager.getCacheFor(mddVariable));
    }

    private MddNode doCompute(
            final MddNode lhs,
            final AbstractNextStateDescriptor nextState,
            final AbstractNextStateDescriptor.Cursor nextStateCursor,
            final MddVariable variable,
            final CacheManager<BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
                            .CacheHolder
                    cache) {
        assert cache != null
                : "Invalid behavior for CacheManager: should have assigned a cache to every"
                        + " variable.";
        if (variable.isNullOrZero(lhs)
                || nextState == AbstractNextStateDescriptor.terminalIdentity()) {
            return lhs;
        }
        if (nextState == null || nextState == AbstractNextStateDescriptor.terminalEmpty()) {
            return variable.getMddGraph().getTerminalZeroNode();
        }

        boolean lhsSkipped = !lhs.isOn(variable);

        if ((lhsSkipped || !variable.isNullOrZero(lhs.defaultValue()))
                && !(lhs.isTerminal()
                        && nextState instanceof AbstractNextStateDescriptor.Postcondition)) {
            throw new UnsupportedOperationException(
                    "Default values are not yet supported in relational product.");
        }

        MddNode ret = cache.getCache().getOrNull(lhs, nextState);
        if (ret != null) {
            return ret;
        }

        final MddStateSpaceInfo stateSpaceInfo = new MddStateSpaceInfo(variable, lhs);

        final IntObjMapView<AbstractNextStateDescriptor> diagonal =
                nextState.getDiagonal(stateSpaceInfo);
        final IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> offDiagonal =
                nextState.getOffDiagonal(stateSpaceInfo);

        IntObjMapView<MddNode> template;

        // Patch to enable initializers
        if (lhs.isTerminal() && nextState instanceof AbstractNextStateDescriptor.Postcondition) {
            template =
                    new IntObjMapViews.Transforming<AbstractNextStateDescriptor, MddNode>(
                            nextState.getDiagonal(stateSpaceInfo),
                            ns ->
                                    ns == null
                                            ? null
                                            : terminalZeroToNull(
                                                    recurse(
                                                            lhs,
                                                            ns,
                                                            nextStateCursor,
                                                            variable,
                                                            cache),
                                                    variable.getMddGraph().getTerminalZeroNode()));
            // } else if (diagonal.isEmpty() && offDiagonal.isEmpty() &&
            // AbstractNextStateDescriptor.isNullOrEmpty(
            // 	offDiagonal.defaultValue())) {
            // 	// Either the ANSD does not affect this level or it is not fireable - will be
            // evaluated in the next call
            // 	// TODO: THIS IS GONNA BE TERRIBLY SLOW
            // 	template = new IntObjMapViews.Transforming<MddNode, MddNode>(lhs,
            // 		(child) -> child == null ? null : terminalZeroToNull(
            // 		recurse(child, diagonal.defaultValue(), variable, cache),
            // 		variable.getMddGraph().getTerminalZeroNode()
            // 	));
        } else {
            MddUnsafeTemplateBuilder templateBuilder =
                    JavaMddFactory.getDefault().createUnsafeTemplateBuilder();
            for (IntObjCursor<? extends MddNode> c = lhs.cursor(); c.moveNext(); ) {
                // TODO we might not need this
                //                try(var valueCursor = nextStateCursor.valueCursor(c.key())) {
                //                    valueCursor.moveTo(c.key());
                //                    final MddNode res = recurse(c.value(), diagonal.get(c.key()),
                // valueCursor, variable, cache);
                //                    final MddNode unioned = unionChildren(res,
                // templateBuilder.get(c.key()), variable);
                //
                //                    templateBuilder.set(c.key(), terminalZeroToNull(unioned,
                // variable.getMddGraph().getTerminalZeroNode()));
                //                }
                try (var valueCursor = nextStateCursor.valueCursor(c.key(), stateSpaceInfo)) {
                    //                  for (IntObjCursor<? extends AbstractNextStateDescriptor>
                    // next = offDiagonal.get(c.key()).cursor(); next.moveNext(); ) {
                    for (; valueCursor.moveNext(); ) {

                        final MddNode res1 =
                                recurse(
                                        c.value(),
                                        valueCursor.value(),
                                        valueCursor,
                                        variable,
                                        cache);
                        final MddNode unioned1 =
                                unionChildren(
                                        res1, templateBuilder.get(valueCursor.key()), variable);

                        templateBuilder.set(
                                valueCursor.key(),
                                terminalZeroToNull(
                                        unioned1, variable.getMddGraph().getTerminalZeroNode()));
                    }
                }

                //				for (IntObjCursor<? extends AbstractNextStateDescriptor> next =
                // offDiagonal.get(c.key()).cursor();
                //				     next.moveNext(); ) {
                //					final MddNode res1 = recurse(c.value(), next.value(), variable, cache);
                //					final MddNode unioned1 = unionChildren(res1, templateBuilder.get(next.key()),
                // variable);
                //
                //					templateBuilder.set(next.key(),
                //						terminalZeroToNull(unioned1, variable.getMddGraph().getTerminalZeroNode())
                //					);
                //				}
            }
            template = templateBuilder.buildAndReset();
        }

        ret = variable.checkInNode(MddStructuralTemplate.of(template));

        cache.getCache().addToCache(lhs, nextState, ret);

        return ret;
    }

    @Override
    public MddNode computeTerminal(
            final MddNode mddNode,
            final AbstractNextStateDescriptor abstractNextStateDescriptor,
            final MddGraph<?> mddGraph) {
        if (mddNode == mddGraph.getTerminalZeroNode() || !abstractNextStateDescriptor.evaluate()) {
            return mddGraph.getTerminalZeroNode();
        }
        return mddNode;
    }

    private MddNode terminalZeroToNull(MddNode node, MddNode terminalZero) {
        return node == terminalZero ? null : node;
    }

    @Override
    public void dispose() {
        this.variableOrder.getMddGraph().unregisterCleanupListener(this);
    }

    @Override
    public void clear() {
        this.cacheManager.clearAll();
    }

    @Override
    public void cleanup() {
        this.cacheManager.forEachCache(
                (cache) ->
                        cache.clearSelectively(
                                (source, ns, result) ->
                                        source.getReferenceCount() == 0
                                                || result.getReferenceCount() == 0));
    }

    private class Aggregator
            implements Consumer<
                    BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>> {
        public long result = 0;
        private final ToLongFunction<
                        BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
                extractor;

        private Aggregator(
                final ToLongFunction<
                                BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
                        extractor) {
            this.extractor = extractor;
        }

        @Override
        public void accept(
                final BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode> cache) {
            result += extractor.applyAsLong(cache);
        }
    }

    public Cache getRelProdCache() {
        class RelProdCache implements Cache {
            private final CacheManager<
                            BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
                    cacheManager;

            RelProdCache(
                    final CacheManager<
                                    BinaryOperationCache<
                                            MddNode, AbstractNextStateDescriptor, MddNode>>
                            cacheManager) {
                this.cacheManager = cacheManager;
            }

            @Override
            public void clear() {
                cacheManager.forEachCache(cache -> cache.clear());
            }

            @Override
            public long getCacheSize() {
                Aggregator a = new Aggregator(c -> c.getCacheSize());
                cacheManager.forEachCache(a);
                return a.result;
            }

            @Override
            public long getQueryCount() {
                Aggregator a = new Aggregator(c -> c.getQueryCount());
                cacheManager.forEachCache(a);
                return a.result;
            }

            @Override
            public long getHitCount() {
                Aggregator a = new Aggregator(c -> c.getHitCount());
                cacheManager.forEachCache(a);
                return a.result;
            }
        }

        return new RelProdCache(cacheManager);
    }
}
