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

import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import java.util.Optional;

public final class BfsProvider implements StateSpaceEnumerationProvider {
    public static boolean verbose = false;

    private final CacheManager<BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
            cacheManager = new CacheManager<>(v -> new BinaryOperationCache<>());
    private final MddVariableOrder variableOrder;
    private final RelationalProductProvider relProdProvider;

    public BfsProvider(final MddVariableOrder variableOrder) {
        this(variableOrder, new LegacyRelationalProductProvider(variableOrder));
    }

    public BfsProvider(
            final MddVariableOrder variableOrder, final RelationalProductProvider relProdProvider) {
        this.variableOrder = variableOrder;
        this.relProdProvider = relProdProvider;
        this.variableOrder.getMddGraph().registerCleanupListener(this);
    }

    public MddHandle compute(
            AbstractNextStateDescriptor.Postcondition initializer,
            AbstractNextStateDescriptor nextStateRelation,
            MddVariableHandle highestAffectedVariable) {

        final MddHandle initialStates =
                relProdProvider.compute(
                        variableOrder.getMddGraph().getHandleForTop(),
                        initializer,
                        highestAffectedVariable);

        MddNode result;

        if (highestAffectedVariable.getVariable().isPresent()) {
            final MddVariable variable = highestAffectedVariable.getVariable().get();
            result = this.compute(initialStates.getNode(), nextStateRelation, variable);
        } else {
            result =
                    this.computeTerminal(
                            initialStates.getNode(),
                            nextStateRelation,
                            highestAffectedVariable.getMddGraph());
        }

        return highestAffectedVariable.getHandleFor(result);
    }

    @Override
    public MddNode compute(
            final MddNode mddNode,
            final AbstractNextStateDescriptor nextStateRelation,
            final MddVariable mddVariable) {
        MddNode res = variableOrder.getMddGraph().getTerminalZeroNode();
        MddNode nextLayer = mddNode;

        while (res != nextLayer) {
            if (verbose) {
                System.out.println("Starting new layer...");
                // System.out.println("Previous result: " + res);
                // System.out.println(GraphvizSerializer.serialize(variableOrder.getDefaultSetSignature().getTopVariableHandle().getHandleFor(res)));
                // System.out.println("New result: " + nextLayer);
                // System.out.println(GraphvizSerializer.serialize(variableOrder.getDefaultSetSignature().getTopVariableHandle().getHandleFor(nextLayer)));
            }
            res = nextLayer;
            final Optional<Iterable<AbstractNextStateDescriptor>> splitNS =
                    nextStateRelation.split();
            if (splitNS.isPresent()) {
                for (AbstractNextStateDescriptor next : splitNS.get()) {
                    if (verbose) {
                        System.out.println("Applying transition: " + next);
                    }
                    nextLayer =
                            mddVariable.union(
                                    nextLayer,
                                    relProdProvider.compute(nextLayer, next, mddVariable));
                }
            } else {
                if (verbose) {
                    System.out.println("Applying transition: " + nextStateRelation);
                }
                nextLayer =
                        mddVariable.union(
                                nextLayer,
                                relProdProvider.compute(nextLayer, nextStateRelation, mddVariable));
            }
        }

        return res;
    }

    @Override
    public MddNode computeTerminal(
            final MddNode mddNode,
            final AbstractNextStateDescriptor nextStateRelation,
            final MddGraph<?> mddGraph) {
        MddNode res = variableOrder.getMddGraph().getTerminalZeroNode();
        MddNode nextLayer = mddNode;

        while (res != nextLayer) {
            nextLayer =
                    mddGraph.unionTerminal(
                            res, relProdProvider.computeTerminal(res, nextStateRelation, mddGraph));
        }

        return res;
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

    public Cache getRelProdCache() {
        return relProdProvider.getRelProdCache();
    }

    @Override
    public long getCacheSize() {
        return getRelProdCache().getCacheSize();
    }

    @Override
    public long getQueryCount() {
        return getRelProdCache().getQueryCount();
    }

    @Override
    public long getHitCount() {
        return getRelProdCache().getHitCount();
    }
}
