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
import com.koloboke.collect.set.hash.HashObjSets;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.ToLongFunction;

public final class SimpleSaturationProvider implements StateSpaceEnumerationProvider {
    public static boolean verbose = false;

    private MddVariableOrder variableOrder;
    private RelationalProductProvider relProdProvider;
    private final CacheManager<SaturationCache> cacheManager =
            new CacheManager<>(v -> new SaturationCache());
    private MddNode terminalZeroNode;

    public SimpleSaturationProvider(final MddVariableOrder variableOrder) {
        this(variableOrder, new LegacyRelationalProductProvider(variableOrder));
    }

    public SimpleSaturationProvider(
            final MddVariableOrder variableOrder, final RelationalProductProvider relProdProvider) {
        this.variableOrder = variableOrder;
        this.relProdProvider = relProdProvider;
        this.variableOrder.getMddGraph().registerCleanupListener(this);
        this.terminalZeroNode = variableOrder.getMddGraph().getTerminalZeroNode();
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

    private MddNode recurse(
            final MddNode mddNode,
            final AbstractNextStateDescriptor nextState,
            MddVariable currentVariable,
            final CacheManager<BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
                            .CacheHolder
                    cache) {
        if (currentVariable.getLower().isPresent()) {
            return compute(mddNode, nextState, currentVariable.getLower().get());
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
            final AbstractNextStateDescriptor nextState,
            final MddVariable mddVariable) {
        return saturate(mddNode, nextState, mddVariable, cacheManager.getCacheFor(mddVariable));
    }

    private MddNode saturate(
            final MddNode n,
            AbstractNextStateDescriptor d,
            MddVariable variable,
            CacheManager<SaturationCache>.CacheHolder cache) {
        if (n.isTerminal()
                || d == AbstractNextStateDescriptor.terminalIdentity()
                || d == AbstractNextStateDescriptor.terminalEmpty()) {
            // TODO this does not handle level skips
            return n;
        }

        MddNode ret = cache.getCache().getSaturateCache().getOrNull(n, d);
        if (ret != null) {
            return ret;
        }

        if (verbose) {
            printIndent();
            System.out.println("Saturating on level " + variable.getTraceInfo() + " with " + d);
        }
        // indent++;

        final MddStateSpaceInfo stateSpaceInfo = new MddStateSpaceInfo(variable, n);

        IntObjMapView<MddNode> satTemplate =
                new IntObjMapViews.Transforming<MddNode, MddNode>(
                        n,
                        (node, key) ->
                                node == null
                                        ? null
                                        : terminalZeroToNull(
                                                saturate(
                                                        node,
                                                        d.getDiagonal(stateSpaceInfo).get(key),
                                                        variable.getLower().orElse(null),
                                                        cache.getLower())));

        MddNode nsat = variable.checkInNode(MddStructuralTemplate.of(satTemplate));

        boolean changed;

        do {
            changed = false;

            final Optional<Iterable<AbstractNextStateDescriptor>> splitNS = d.split();
            if (splitNS.isPresent()) {
                for (AbstractNextStateDescriptor dfire : splitNS.get()) {
                    // System.out.println("Applying transition: " + dfire);
                    if (dfire.isLocallyIdentity(stateSpaceInfo)) {
                        continue;
                    }
                    MddNode nfire = satFire(nsat, d, dfire, variable, cache);

                    nfire = variable.union(nsat, nfire);

                    if (nfire != nsat) {
                        nsat = nfire;
                        changed = true;
                    }
                }
            } else if (!d.isLocallyIdentity(stateSpaceInfo)) {
                // System.out.println("Applying transition: " + d);
                MddNode nfire = satFire(nsat, d, d, variable, cache);

                nfire = variable.union(nsat, nfire);

                if (nfire != nsat) {
                    nsat = nfire;
                    changed = true;
                }
            }
        } while (changed);

        cache.getCache().getSaturateCache().addToCache(n, d, nsat);

        if (verbose) {
            indent--;
            printIndent();
            System.out.println(
                    "Done Saturating on level "
                            + variable.getTraceInfo()
                            + " resulting in "
                            + nsat);
        }

        // indent--;
        // printIndent();
        // System.out.println("Saturated level " + variable.getTraceInfo() + ", domain size is " +
        // variable.getDomainSize());
        //
        return nsat;
    }

    private MddNode satFire(
            MddNode n,
            AbstractNextStateDescriptor dsat,
            AbstractNextStateDescriptor dfire,
            MddVariable variable,
            CacheManager<SaturationCache>.CacheHolder cache) {
        if (n == terminalZeroNode || dfire == AbstractNextStateDescriptor.terminalEmpty()) {
            return terminalZeroNode;
        }

        if (dfire == AbstractNextStateDescriptor.terminalIdentity()) {
            return n;
        }

        boolean lhsSkipped = !n.isOn(variable);

        if (verbose) {
            printIndent();
            System.out.println(
                    "SatFire on level "
                            + variable.getTraceInfo()
                            + " with dsat="
                            + dsat
                            + "; dfire="
                            + dfire);
            indent++;
        }

        MddUnsafeTemplateBuilder templateBuilder =
                JavaMddFactory.getDefault().createUnsafeTemplateBuilder();

        final MddStateSpaceInfo stateSpaceInfo = new MddStateSpaceInfo(variable, n);

        final IntObjMapView<AbstractNextStateDescriptor> diagonal =
                dfire.getDiagonal(stateSpaceInfo);
        final IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> offDiagonal =
                dfire.getOffDiagonal(stateSpaceInfo);

        final RecursiveIntObjMapView<? extends MddNode> lhsInterpreter;
        if ((lhsSkipped || (n.defaultValue() != null && n.isEmpty())) && !variable.isBounded()) {
            final MddNode childCandidate = lhsSkipped ? n : n.defaultValue();
            // We use the keyset of the ANSD to trim
            lhsInterpreter =
                    RecursiveIntObjMapView.of(
                            IntObjMapView.empty(childCandidate).trim(offDiagonal.keySet()));
        } else {
            lhsInterpreter =
                    variable.getNodeInterpreter(
                            n); // using the interpreter might cause a performance overhead
        }
        for (IntObjCursor<? extends MddNode> cFrom = lhsInterpreter.cursor(); cFrom.moveNext(); ) {

            // Identity step
            final AbstractNextStateDescriptor diagonalContinuation = diagonal.get(cFrom.key());
            if (!AbstractNextStateDescriptor.isNullOrEmpty(diagonalContinuation)) {

                if (verbose) {
                    System.out.println("Potential step: " + cFrom.key() + "->" + cFrom.key());
                }

                MddNode s =
                        relProd(
                                cFrom.value(),
                                dsat.getDiagonal(stateSpaceInfo).defaultValue(),
                                diagonalContinuation,
                                variable.getLower().orElse(null),
                                cache.getLower());

                if (s != terminalZeroNode) {
                    // confirm(variable, cFrom.key());

                    templateBuilder.set(
                            cFrom.key(),
                            terminalZeroToNull(
                                    unionChildren(templateBuilder.get(cFrom.key()), s, variable)));
                }
            }

            for (IntObjCursor<? extends AbstractNextStateDescriptor> cTo =
                            offDiagonal.get(cFrom.key()).cursor();
                    cTo.moveNext(); ) {
                if (cFrom.key() == cTo.key()) {
                    continue;
                }

                if (verbose) {
                    System.out.println("Potential step: " + cFrom.key() + "->" + cTo.key());
                }

                assert cFrom.value() != terminalZeroNode;
                assert cTo.value() != AbstractNextStateDescriptor.terminalEmpty();

                MddNode s =
                        relProd(
                                cFrom.value(),
                                // Level skip will be encoded as default value
                                dsat.getDiagonal(stateSpaceInfo).defaultValue(),
                                cTo.value(),
                                variable.getLower().orElse(null),
                                cache.getLower());

                if (s != terminalZeroNode) {
                    confirm(variable, cTo.key());

                    templateBuilder.set(
                            cTo.key(),
                            terminalZeroToNull(
                                    unionChildren(templateBuilder.get(cTo.key()), s, variable)));
                }
            }
        }

        final var template = templateBuilder.buildAndReset();
        if (!template.isEmpty())
            Preconditions.checkArgument(
                    n.defaultValue() == null, "Default value is not supported with explicit edges");
        MddNode ret = variable.checkInNode(MddStructuralTemplate.of(template));

        if (verbose) {
            indent--;
            printIndent();
            System.out.println(
                    "Done SatFire on level " + variable.getTraceInfo() + " resulting in " + ret);
        }

        return ret;
    }

    private MddNode relProd(
            MddNode n,
            AbstractNextStateDescriptor dsat,
            AbstractNextStateDescriptor dfire,
            MddVariable variable,
            CacheManager<SaturationCache>.CacheHolder cache) {
        if (n == terminalZeroNode || dfire == AbstractNextStateDescriptor.terminalEmpty()) {
            return terminalZeroNode;
        }

        if (dfire == AbstractNextStateDescriptor.terminalIdentity()) {
            return n;
        }

        if (n.isTerminal() && dfire.evaluate()) {
            return n;
        }

        boolean lhsSkipped = !n.isOn(variable);

        final MddStateSpaceInfo stateSpaceInfo = new MddStateSpaceInfo(variable, n);

        MddNode ret = cache.getCache().getRelProdCache().getOrNull(n, dsat, dfire);
        if (ret != null) {
            return ret;
        }

        if (verbose) {
            printIndent();
            System.out.println(
                    "SatRelProd on level "
                            + variable.getTraceInfo()
                            + ", node="
                            + n
                            + ", with dsat="
                            + dsat
                            + "; dfire"
                            + "="
                            + dfire);
            indent++;
        }

        MddUnsafeTemplateBuilder templateBuilder =
                JavaMddFactory.getDefault().createUnsafeTemplateBuilder();

        final IntObjMapView<AbstractNextStateDescriptor> diagonal =
                dfire.getDiagonal(stateSpaceInfo);
        final IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> offDiagonal =
                dfire.getOffDiagonal(stateSpaceInfo);

        final RecursiveIntObjMapView<? extends MddNode> lhsInterpreter;
        if ((lhsSkipped || (n.defaultValue() != null && n.isEmpty())) && !variable.isBounded()) {
            final MddNode childCandidate = lhsSkipped ? n : n.defaultValue();
            // We use the keyset of the ANSD to trim
            lhsInterpreter =
                    RecursiveIntObjMapView.of(
                            IntObjMapView.empty(childCandidate).trim(offDiagonal.keySet()));
        } else {
            lhsInterpreter =
                    variable.getNodeInterpreter(
                            n); // using the interpreter might cause a performance overhead
        }
        for (IntObjCursor<? extends MddNode> cFrom = lhsInterpreter.cursor(); cFrom.moveNext(); ) {
            // Identity step
            final AbstractNextStateDescriptor diagonalContinuation = diagonal.get(cFrom.key());
            if (!AbstractNextStateDescriptor.isNullOrEmpty(diagonalContinuation)) {

                if (verbose) {
                    System.out.println("Potential step: " + cFrom.key() + "->" + cFrom.key());
                }

                MddNode s =
                        relProd(
                                cFrom.value(),
                                dsat.getDiagonal(stateSpaceInfo).defaultValue(),
                                diagonalContinuation,
                                variable.getLower().orElse(null),
                                cache.getLower());

                if (s != terminalZeroNode) {
                    // confirm(variable, cFrom.key());

                    templateBuilder.set(
                            cFrom.key(),
                            terminalZeroToNull(
                                    unionChildren(templateBuilder.get(cFrom.key()), s, variable)));
                }
            }

            for (IntObjCursor<? extends AbstractNextStateDescriptor> cTo =
                            offDiagonal.get(cFrom.key()).cursor();
                    cTo.moveNext(); ) {
                if (cFrom.key() == cTo.key()) {
                    continue;
                }

                if (verbose) {
                    System.out.println("Potential step: " + cFrom.key() + "->" + cTo.key());
                }

                assert cFrom.value() != terminalZeroNode;
                assert cTo.value() != AbstractNextStateDescriptor.terminalEmpty();

                MddNode s =
                        relProd(
                                cFrom.value(),
                                dsat.getDiagonal(stateSpaceInfo).defaultValue(),
                                cTo.value(),
                                variable.getLower().orElse(null),
                                cache.getLower());

                if (s != terminalZeroNode) {
                    confirm(variable, cTo.key());

                    templateBuilder.set(
                            cTo.key(),
                            terminalZeroToNull(
                                    unionChildren(templateBuilder.get(cTo.key()), s, variable)));
                }
            }
        }

        final var template = templateBuilder.buildAndReset();
        if (!template.isEmpty())
            Preconditions.checkArgument(
                    n.defaultValue() == null, "Default value is not supported with explicit edges");
        ret = variable.checkInNode(MddStructuralTemplate.of(template));

        ret = saturate(ret, dsat, variable, cache);

        cache.getCache().getRelProdCache().addToCache(n, dsat, dfire, ret);

        if (verbose) {
            indent--;
            printIndent();
            System.out.println(
                    "Done SatRelProd on level " + variable.getTraceInfo() + " resulting in " + ret);
        }

        return ret;
    }

    private void confirm(final MddVariable variable, final int key) {}

    @Override
    public MddNode computeTerminal(
            final MddNode mddNode,
            final AbstractNextStateDescriptor nextState,
            final MddGraph<?> mddGraph) {
        return mddNode;
    }

    private MddNode terminalZeroToNull(MddNode node) {
        return node == terminalZeroNode ? null : node;
    }

    private int indent = 0;

    private void printIndent() {
        for (int i = 0; i < indent; ++i) {
            System.out.print(" ");
        }
    }

    @Override
    public void dispose() {
        this.variableOrder.getMddGraph().unregisterCleanupListener(this);
    }

    @Override
    public void clear() {
        cacheManager.clearAll();
    }

    @Override
    public void cleanup() {
        this.cacheManager.forEachCache(
                (cache) -> {
                    cache.getSaturateCache()
                            .clearSelectively(
                                    (source, ns1, result) ->
                                            source.getReferenceCount() == 0
                                                    || result.getReferenceCount() == 0);
                    cache.getRelProdCache()
                            .clearSelectively(
                                    (source, ns1, ns2, result) ->
                                            source.getReferenceCount() == 0
                                                    || result.getReferenceCount() == 0);
                });
    }

    private class Aggregator implements Consumer<SaturationCache> {
        public long result = 0;
        private final ToLongFunction<SaturationCache> extractor;

        private Aggregator(final ToLongFunction<SaturationCache> extractor) {
            this.extractor = extractor;
        }

        @Override
        public void accept(final SaturationCache cache) {
            result += extractor.applyAsLong(cache);
        }
    }

    public Cache getSaturateCache() {
        class SaturateCache implements Cache {
            private final CacheManager<SaturationCache> cacheManager;

            SaturateCache(final CacheManager<SaturationCache> cacheManager) {
                this.cacheManager = cacheManager;
            }

            @Override
            public void clear() {
                cacheManager.forEachCache(cache -> cache.getSaturateCache().clear());
            }

            @Override
            public long getCacheSize() {
                Aggregator a = new Aggregator(c -> c.getSaturateCache().getCacheSize());
                cacheManager.forEachCache(a);
                return a.result;
            }

            @Override
            public long getQueryCount() {
                Aggregator a = new Aggregator(c -> c.getSaturateCache().getQueryCount());
                cacheManager.forEachCache(a);
                return a.result;
            }

            @Override
            public long getHitCount() {
                Aggregator a = new Aggregator(c -> c.getSaturateCache().getHitCount());
                cacheManager.forEachCache(a);
                return a.result;
            }
        }

        return new SaturateCache(cacheManager);
    }

    // TODO: HAXXXX DON'T DO THIS EVER AGAIN
    public Set<MddNode> getSaturatedNodes() {
        final Set<MddNode> ret = HashObjSets.newUpdatableSet();
        cacheManager.forEachCache(
                (c) ->
                        c.getSaturateCache()
                                .clearSelectively(
                                        (source, ns, result) -> {
                                            ret.add(result);
                                            return false;
                                        }));
        return ret;
    }

    public Cache getRelProdCache() {
        class RelProdCache implements Cache {
            private final CacheManager<SaturationCache> cacheManager;

            RelProdCache(final CacheManager<SaturationCache> cacheManager) {
                this.cacheManager = cacheManager;
            }

            @Override
            public void clear() {
                cacheManager.forEachCache(cache -> cache.getRelProdCache().clear());
            }

            @Override
            public long getCacheSize() {
                Aggregator a = new Aggregator(c -> c.getRelProdCache().getCacheSize());
                cacheManager.forEachCache(a);
                return a.result;
            }

            @Override
            public long getQueryCount() {
                Aggregator a = new Aggregator(c -> c.getRelProdCache().getQueryCount());
                cacheManager.forEachCache(a);
                return a.result;
            }

            @Override
            public long getHitCount() {
                Aggregator a = new Aggregator(c -> c.getRelProdCache().getHitCount());
                cacheManager.forEachCache(a);
                return a.result;
            }
        }

        return new RelProdCache(cacheManager);
    }

    @Override
    public long getCacheSize() {
        return getSaturateCache().getCacheSize();
    }

    @Override
    public long getQueryCount() {
        return getSaturateCache().getQueryCount();
    }

    @Override
    public long getHitCount() {
        return getSaturateCache().getHitCount();
    }
}
