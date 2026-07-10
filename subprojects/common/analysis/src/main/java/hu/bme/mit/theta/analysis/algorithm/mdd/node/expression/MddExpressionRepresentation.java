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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.hash.HashIntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import com.koloboke.collect.set.hash.HashIntSet;
import com.koloboke.collect.set.hash.HashIntSets;
import hu.bme.mit.delta.collections.*;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation;
import hu.bme.mit.theta.analysis.algorithm.mdd.mddtoexpr.MddToExprUtilKt;
import hu.bme.mit.theta.common.GrowingIntArray;
import hu.bme.mit.theta.common.exception.NotSolvableException;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.io.Closeable;
import java.util.*;

public class MddExpressionRepresentation implements RecursiveIntObjMapView<MddNode> {

    private final Expr<BoolType> expr;
    private final Decl<?> decl;
    private final MddVariable mddVariable;

    private Traverser lazyTraverser;
    private final ExplicitRepresentation explicitRepresentation;

    private final SolverPool solverPool;
    private final boolean transExpr;
    // never query the solver: decide every edge by substitution, treating an undetermined result as
    // absent (matches the witness classification of seeding). Used by the seeding constraint nodes.
    private final boolean substitutionOnly;
    // the lookahead strategy is attached per graph (run-scoped), defaulting to VARIABLE_LEVEL
    public static final MddGraph.Key<MddToExprStrategy> LOOK_AHEAD =
            new MddGraph.Key<>("lookAheadStrategy");

    public enum MddToExprStrategy {
        NONE {
            @Override
            public Expr<BoolType> toExpr(MddHandle handle) {
                return True();
            }
        },
        NODE_LEVEL {
            @Override
            public Expr<BoolType> toExpr(MddHandle handle) {
                return MddToExprUtilKt.toExprNodeLevel(handle);
            }
        },
        VARIABLE_LEVEL {
            @Override
            public Expr<BoolType> toExpr(MddHandle handle) {
                return MddToExprUtilKt.toApproximationExprVariableLevel(handle);
            }
        },
        VECTOR_LEVEL {
            @Override
            public Expr<BoolType> toExpr(MddHandle handle) {
                return MddToExprUtilKt.toExprVectorLevel(handle);
            }
        };

        public abstract Expr<BoolType> toExpr(MddHandle handle);
    }

    private MddExpressionRepresentation(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final MddVariable mddVariable,
            final SolverPool solverPool,
            final boolean transExpr,
            final boolean substitutionOnly) {
        this.expr = expr;
        this.decl = decl;
        this.mddVariable = mddVariable;
        this.solverPool = solverPool;
        this.explicitRepresentation = new ExplicitRepresentation();
        this.transExpr = transExpr;
        this.substitutionOnly = substitutionOnly;
    }

    /** Read-only view of this node's explored structure, for consumers that must not mutate it. */
    public Explored explored() {
        return explicitRepresentation;
    }

    public static MddExpressionRepresentation of(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final MddVariable mddVariable,
            final SolverPool solverPool,
            final boolean transExpr) {
        return new MddExpressionRepresentation(
                expr, decl, mddVariable, solverPool, transExpr, false);
    }

    public static MddExpressionRepresentation of(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final MddVariable mddVariable,
            final SolverPool solverPool,
            final boolean transExpr,
            final Valuation satModel,
            final boolean substitutionOnly) {
        final var repr =
                new MddExpressionRepresentation(
                        expr, decl, mddVariable, solverPool, transExpr, substitutionOnly);
        if (satModel != null) {
            repr.getLazyTraverser().cacheModel(satModel);
        }
        return repr;
    }

    public static MddExpressionRepresentation ofDefault(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final MddVariable mddVariable,
            final SolverPool solverPool,
            final MddNode defaultValue,
            final boolean transExpr,
            final boolean substitutionOnly) {
        final MddExpressionRepresentation representation =
                new MddExpressionRepresentation(
                        expr, decl, mddVariable, solverPool, transExpr, substitutionOnly);
        representation.explicitRepresentation.cacheDefault(defaultValue);
        representation.explicitRepresentation.setComplete();
        return representation;
    }

    public static MddExpressionRepresentation ofDetermined(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final MddVariable mddVariable,
            final SolverPool solverPool,
            final int key,
            final MddNode childNode,
            final boolean transExpr,
            final boolean substitutionOnly) {
        final MddExpressionRepresentation representation =
                new MddExpressionRepresentation(
                        expr, decl, mddVariable, solverPool, transExpr, substitutionOnly);
        if (!mddVariable.isNullOrZero(childNode)) {
            representation.explicitRepresentation.cacheNode(key, childNode);
        }
        representation.explicitRepresentation.setComplete();
        return representation;
    }

    public Expr<BoolType> getExpr() {
        return expr;
    }

    public Decl<?> getDecl() {
        return decl;
    }

    public MddVariable getMddVariable() {
        return mddVariable;
    }

    private Traverser getLazyTraverser() {
        if (lazyTraverser == null) lazyTraverser = Traverser.create(this, solverPool);
        return lazyTraverser;
    }

    /** Seeds the explicit caches along {@code model}, which must satisfy {@link #getExpr()}. */
    public void cacheModel(Valuation model) {
        cacheModel(model, null, new IdentityHashMap<>());
    }

    /**
     * Caches the known structure {@code source} into this node.
     */
    public void cacheModel(Valuation prefix, MddNode source) {
        cacheModel(prefix, source, new IdentityHashMap<>());
    }

    private void cacheModel(
            Valuation prefix,
            MddNode source,
            IdentityHashMap<MddExpressionRepresentation, Set<MddNode>> done) {
        while (source != null && source.getRepresentation() instanceof IdentityRepresentation) {
            // an identity pair in source: this node's expression proves the same pair identical, so
            // cacheChild has already unwrapped past both levels — the source follows suit
            source = ((IdentityRepresentation) source.getRepresentation()).getContinuation();
        }
        if (source != null && source.isTerminal()) {
            return;
        }
        final MddNode existingDefault = explicitRepresentation.getCacheView().defaultValue();
        if (existingDefault != null) {
            // already a skip level: descend its default, the source unchanged
            final MddExpressionRepresentation child = childRepresentation(existingDefault);
            if (child != null) child.cacheModel(prefix, source, done);
            return;
        }
        final Optional<? extends LitExpr<?>> lit = prefix.eval(decl);
        if (lit.isPresent()) {
            final MddExpressionRepresentation child =
                    cacheChild(LitExprConverter.toInt(lit.get()), true);
            if (child != null) child.cacheModel(prefix, source, done);
            return;
        }
        if (source == null) {
            // plain valuation, unassigned level: don't-care, the level stays explorable
            final MddExpressionRepresentation child = cacheChild(0, false);
            if (child != null) child.cacheModel(prefix, null, done);
            return;
        }
        // below the prefix: mirror source's structure, memoized so a shared sub-DAG (a compact MDD has
        // exponentially many paths) is walked once per node, not once per path
        if (!done.computeIfAbsent(this, k -> new HashSet<>()).add(source)) {
            return;
        }
        for (var cursor = source.cursor(); cursor.moveNext(); ) {
            final MddExpressionRepresentation child = cacheChild(cursor.key(), true);
            if (child != null) child.cacheModel(prefix, (MddNode) cursor.value(), done);
        }
        final MddNode sourceDefault = source.defaultValue();
        if (sourceDefault != null) {
            // a don't-care level in source: keep this level explorable, descend
            final MddExpressionRepresentation child = cacheChild(0, false);
            if (child != null) child.cacheModel(prefix, sourceDefault, done);
        }
    }

    /**
     * Builds the explorable expression child for {@code key} (its expression substituted), caching the
     * edge when {@code cacheEdge}; returns its representation, or null at a terminal/identity bottom.
     */
    private MddExpressionRepresentation cacheChild(int key, boolean cacheEdge) {
        MddNode childNode = cacheEdge ? explicitRepresentation.getCacheView().get(key) : null;
        if (childNode == null) {
            final Expr<BoolType> substituted =
                    cacheEdge
                            ? ExprUtils.simplify(
                                    expr,
                                    ImmutableValuation.builder()
                                            .put(decl, LitExprConverter.toLitExpr(key, decl.getType()))
                                            .build())
                            : expr;
            if (mddVariable.getLower().isPresent()) {
                childNode =
                        mddVariable
                                .getLower()
                                .get()
                                .checkInNode(
                                        MddExpressionTemplate.ofKnownSat(
                                                substituted, o -> (Decl) o, solverPool, transExpr));
            } else {
                childNode = ((MddGraph<Expr>) mddVariable.getMddGraph()).getNodeFor(True());
            }
            if (cacheEdge
                    && !explicitRepresentation.isComplete()
                    && explicitRepresentation.getCacheView().defaultValue() == null
                    && !mddVariable.isNullOrZero(childNode)) {
                explicitRepresentation.cacheNode(key, childNode);
                completeIfBoolFullyCached();
            }
        }
        return childRepresentation(childNode);
    }

    /** The expression node a child resolves to, unwrapping identity levels; null at a terminal. */
    private static MddExpressionRepresentation childRepresentation(MddNode childNode) {
        if (childNode.isTerminal()) return null;
        var repr = childNode.getRepresentation();
        while (repr instanceof IdentityRepresentation) {
            final MddNode cont = ((IdentityRepresentation) repr).getContinuation();
            if (cont.isTerminal()) return null;
            repr = cont.getRepresentation();
        }
        return (MddExpressionRepresentation) repr;
    }

    /** A bool decl has exactly the keys 0 and 1, so deciding both makes the node complete. */
    public void completeIfBoolFullyCached() {
        if (decl.getType() instanceof BoolType
                && !explicitRepresentation.isComplete()
                && explicitRepresentation.getCacheView().defaultValue() == null
                && (explicitRepresentation.getCacheView().containsKey(0)
                        || explicitRepresentation.isNegativelyCached(0))
                && (explicitRepresentation.getCacheView().containsKey(1)
                        || explicitRepresentation.isNegativelyCached(1))) {
            explicitRepresentation.setComplete();
        }
    }

    @Override
    public boolean isEmpty() {
        //        return false;
        return explicitRepresentation.isComplete() && size() == 0;
    }

    @Override
    public boolean isProcedural() {
        return !explicitRepresentation.isComplete();
    }

    @Override
    public boolean containsKey(int key) {
        return getLazyTraverser().queryEdge(key);
    }

    public boolean isTransExpr() {
        return this.transExpr;
    }

    @Override
    public MddNode get(int key) {
        final var cached = explicitRepresentation.getCacheView().get(key);
        if (cached != null || this.explicitRepresentation.isComplete()) {
            if (cached != null) explicitRepresentation.markVisited(key);
            return cached;
        }
        if (explicitRepresentation.isNegativelyCached(key)) return null;

        final MutableValuation val = new MutableValuation();
        final LitExpr<?> litExpr = LitExprConverter.toLitExpr(key, decl.getType());
        if (litExpr.isInvalid()) {
            explicitRepresentation.cacheNegative(key);
            completeIfBoolFullyCached();
            return null;
        }

        val.put(decl, litExpr);
        Expr<BoolType> simplifiedExpr;
        try {
            simplifiedExpr = ExprUtils.simplify(expr, val);
        } catch (ArithmeticException e) {
            // This is needed for division by zero cases
            simplifiedExpr = False();
        }

        final MddNode childNode;
        if (mddVariable.getLower().isPresent()) {
            final MddExpressionTemplate template =
                    substitutionOnly
                            ? MddExpressionTemplate.ofSubstitution(
                                    simplifiedExpr, o -> (Decl) o, solverPool, transExpr)
                            : MddExpressionTemplate.of(
                                    simplifiedExpr, o -> (Decl) o, solverPool, transExpr);
            childNode = mddVariable.getLower().get().checkInNode(template);
        } else {
            final Expr<BoolType> canonizedExpr =
                    ExprUtils.canonize(ExprUtils.simplify(simplifiedExpr));
            MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();

            if (canonizedExpr instanceof FalseExpr) {
                childNode = null;
            } else if (canonizedExpr instanceof TrueExpr) {
                childNode = mddGraph.getNodeFor(True());
            } else if (substitutionOnly) {
                // substitution left the bottom expression undetermined: treat as absent, never solve
                childNode = null;
            } else {
                var solver = solverPool.requestSolver();
                try (var wpp = new WithPushPop(solver)) {
                    solver.add(canonizedExpr);
                    if (solver.check().isSat()) {
                        // TODO replace this with canonizedExpr if remainder expression is needed
                        childNode = mddGraph.getNodeFor(True());
                    } else {
                        childNode = null;
                    }
                }
            }
        }
        if (!mddVariable.isNullOrZero(childNode)) {
            explicitRepresentation.cacheNode(key, childNode);
            explicitRepresentation.markVisited(key);
        } else {
            // also for the zero node of a non-bottom level: the absence must land in the
            // explicit caches for later iterations' bounds to see it
            explicitRepresentation.cacheNegative(key);
        }
        completeIfBoolFullyCached();
        return childNode;
    }

    @Override
    public MddNode defaultValue() {
        return explicitRepresentation.getCacheView().defaultValue();
    }

    @Override
    public RecursiveIntObjCursor<? extends MddNode> cursor() {
        return new Cursor(null, Traverser.create(this, solverPool));
    }

    @Override
    public RecursiveIntObjCursor<? extends MddNode> cursor(RecursiveIntObjMapView<?> constraint) {
        Preconditions.checkArgument(constraint instanceof MddHandle);
        final MddHandle mddHandle = (MddHandle) constraint;

        var strategy = mddVariable.getMddGraph().getAttribute(LOOK_AHEAD);
        if (strategy == null) {
            strategy = MddToExprStrategy.VARIABLE_LEVEL;
        }
        final var constraintExpr = strategy.toExpr(mddHandle);

        return new Cursor(null, Traverser.create(this, constraintExpr, solverPool));
    }

    @Override
    public int size() {
        if (explicitRepresentation.isComplete())
            return explicitRepresentation.getCacheView().size();
        return -1;
    }

    @Override
    public String toString() {
        return expr.toString() + ", " + decl.toString();
    }

    @Override
    public boolean equals(Object that) {
        if (this == that) return true;
        if (that instanceof MddExpressionRepresentation) {
            return Objects.equals(mddVariable, ((MddExpressionRepresentation) that).mddVariable)
                    && Objects.equals(decl, ((MddExpressionRepresentation) that).decl)
                    && (Objects.equals(expr, ((MddExpressionRepresentation) that).expr)
                            || semanticEquals(that));
        }
        if (that instanceof MddNode) {
            return this.equals(((MddNode) that).getRepresentation());
        }
        return false;
    }

    private boolean semanticEquals(Object that) {

        if (that instanceof MddExpressionRepresentation thatRepresentation) {
            if (this.explicitRepresentation.complete
                    && thatRepresentation.explicitRepresentation.complete) {
                return IntObjMapView.equals(
                        this.explicitRepresentation.getCacheView(),
                        thatRepresentation.explicitRepresentation.getCacheView());
            }
        } else if (that instanceof IntObjMapView<?> thatView) {
            if (this.explicitRepresentation.complete) {
                return IntObjMapView.equals(thatView, this.explicitRepresentation.getCacheView());
            }
        }
        return false;
    }

    @Override
    public int hashCode() {
        return Objects.hash(expr, decl, mddVariable);
    }

    /**
     * Read-only view of what exploration has established about an expression node: the edges and
     * default it has cached so far (a lower bound on the node's edges), the keys proven absent, and
     * whether exploration has exhausted the node. None of the cache's mutators are reachable here.
     */
    public interface Explored {
        IntObjMapView<MddNode> knownEdges();

        IntSetView knownAbsentKeys();

        IntSetView visitedKeys();

        boolean isComplete();
    }

    static class ExplicitRepresentation implements Explored {
        private final HashIntObjMap<MddNode> cache;
        private final GrowingIntArray edgeOrdering;
        private final HashIntSet negativeCache;
        private final HashIntSet visited;
        private MddNode defaultValue;
        private boolean complete;

        public ExplicitRepresentation() {
            this.cache = HashIntObjMaps.newUpdatableMap();
            this.edgeOrdering = new GrowingIntArray(100, 100);
            this.negativeCache = HashIntSets.newUpdatableSet();
            this.visited = HashIntSets.newUpdatableSet();
            this.defaultValue = null;
            this.complete = false;
        }

        void cacheNode(int key, MddNode node) {
            Preconditions.checkState(!complete);
            Preconditions.checkState(defaultValue == null);
            if (this.cache.size() > 1000) {
                throw new NotSolvableException();
            }
            this.cache.put(key, node);
            this.edgeOrdering.add(key);
        }

        void cacheNegative(int key) {
            negativeCache.add(key);
        }

        void markVisited(int key) {
            visited.add(key);
        }

        @Override
        public IntSetView visitedKeys() {
            return IntSetView.of(visited);
        }

        public boolean isNegativelyCached(int key) {
            return negativeCache.contains(key);
        }

        public HashIntSet getNegativeKeys() {
            return negativeCache;
        }

        void cacheDefault(MddNode defaultValue) {
            Preconditions.checkState(!complete);
            this.defaultValue = defaultValue;
        }

        void setComplete() {
            this.complete = true;
        }

        public IntObjMapView<MddNode> getCacheView() {
            return IntObjMapView.of(cache, defaultValue);
        }

        @Override
        public boolean isComplete() {
            return complete;
        }

        @Override
        public IntObjMapView<MddNode> knownEdges() {
            return getCacheView();
        }

        @Override
        public IntSetView knownAbsentKeys() {
            return IntSetView.of(negativeCache);
        }

        public int getEdge(int index) {
            return edgeOrdering.get(index);
        }

        public int getSize() {
            return edgeOrdering.getSize();
        }
    }

    private static class Traverser implements Closeable {

        private MddExpressionRepresentation currentRepresentation;
        private final Expr<BoolType> constraint;
        private boolean constraintApplied;

        private final SolverPool solverPool;
        private Solver solver;

        private final Stack<MddExpressionRepresentation> stack;

        // Tracks whether the solver has a persistent push level with the
        // base expression + accumulated negations for the current level
        private boolean enumerationActive = false;

        private Traverser(
                MddExpressionRepresentation rootRepresentation,
                Expr<BoolType> constraint,
                SolverPool solverPool) {
            this.solverPool = solverPool;
            this.stack = new Stack<>();
            this.constraint = constraint;
            this.currentRepresentation = rootRepresentation;
            this.constraintApplied = false;
        }

        public static Traverser create(
                MddExpressionRepresentation rootRepresentation,
                Expr<BoolType> constraint,
                SolverPool solverPool) {
            return new Traverser(rootRepresentation, constraint, solverPool);
        }

        public static Traverser create(
                MddExpressionRepresentation rootRepresentation, SolverPool solverPool) {
            return new Traverser(rootRepresentation, True(), solverPool);
        }

        private void stopEnumeration() {
            if (enumerationActive && solver != null) {
                solver.pop();
                enumerationActive = false;
            }
        }

        public MddExpressionRepresentation moveUp() {
            Preconditions.checkState(stack.size() > 0);
            setCurrentRepresentation(stack.pop());
            return currentRepresentation;
        }

        public boolean queryEdge(int assignment) {
            if (currentRepresentation
                    .explicitRepresentation
                    .getCacheView()
                    .keySet()
                    .contains(assignment)) {
                currentRepresentation.explicitRepresentation.markVisited(assignment);
                return true;
            }
            if (currentRepresentation.explicitRepresentation.getCacheView().defaultValue() != null)
                return true;
            if (currentRepresentation.explicitRepresentation.isNegativelyCached(assignment))
                return false;
            if (!currentRepresentation.explicitRepresentation.isComplete()) {

                if (currentRepresentation.substitutionOnly) {
                    // decide and cache the edge by substitution (get is solver-free here)
                    return currentRepresentation.get(assignment) != null;
                }

                if (solver == null) solver = solverPool.requestSolver();

                final SolverStatus status;
                final Valuation model;
                final LitExpr<?> litExpr =
                        LitExprConverter.toLitExpr(
                                assignment, currentRepresentation.decl.getType());
                try (WithPushPop wpp = new WithPushPop(solver)) {
                    if (!enumerationActive) {
                        solver.add(currentRepresentation.expr);
                    }
                    solver.add(Eq(currentRepresentation.decl.getRef(), litExpr));
                    solver.check();
                    status = solver.getStatus();
                    model = status.isSat() ? solver.getModel() : null;
                }
                Preconditions.checkNotNull(status);
                if (status.isSat()) {
                    cacheModel(model);
                    currentRepresentation.explicitRepresentation.markVisited(assignment);
                    return true;
                } else {
                    currentRepresentation.explicitRepresentation.cacheNegative(assignment);
                    currentRepresentation.completeIfBoolFullyCached();
                }
            }
            return false;
        }

        public MddNode peekDown(int assignment) {
            queryEdge(assignment);
            return currentRepresentation.explicitRepresentation.getCacheView().get(assignment);
        }

        public QueryResult queryEdge() {
            if (!currentRepresentation.explicitRepresentation.isComplete()) {

                if (solver == null) solver = solverPool.requestSolver();

                if (!enumerationActive) {
                    solver.push();
                    solver.add(currentRepresentation.expr);
                    for (var cur =
                                    currentRepresentation
                                            .explicitRepresentation
                                            .getCacheView()
                                            .cursor();
                            cur.moveNext(); ) {
                        solver.add(
                                Neq(
                                        currentRepresentation.decl.getRef(),
                                        LitExprConverter.toLitExpr(
                                                cur.key(), currentRepresentation.decl.getType())));
                    }
                    if (currentRepresentation.explicitRepresentation.getCacheView().size() >= 5) {
                        solver.add(constraint);
                        constraintApplied = true;
                    }
                    enumerationActive = true;
                }

                // Lazily add constraint once the 5th edge has been cached
                if (!constraintApplied
                        && currentRepresentation.explicitRepresentation.getCacheView().size()
                                >= 5) {
                    solver.add(constraint);
                    constraintApplied = true;
                }

                solver.check();
                final SolverStatus status = solver.getStatus();
                final Valuation model = status.isSat() ? solver.getModel() : null;

                if (status.isSat()) {
                    final Decl<?> decl = currentRepresentation.decl;
                    final Optional<? extends LitExpr<?>> optionalLitExpr = model.eval(decl);

                    final LitExpr<?> literal;
                    final Valuation modelToCache;
                    if (optionalLitExpr.isPresent()) {
                        literal = optionalLitExpr.get();
                        modelToCache = model;
                    } else {
                        final int newValue;
                        if (currentRepresentation.mddVariable.isBounded()) {
                            final IntSetView domain =
                                    IntSetView.range(
                                            0, currentRepresentation.mddVariable.getDomainSize());
                            final IntSetView remaining =
                                    domain.minus(
                                            currentRepresentation
                                                    .explicitRepresentation
                                                    .getCacheView()
                                                    .keySet());
                            if (remaining.isEmpty()) {
                                stopEnumeration();
                                currentRepresentation.explicitRepresentation.setComplete();
                                return QueryResult.failed();
                            } else {
                                final var cur = remaining.cursor();
                                Preconditions.checkState(cur.moveNext());
                                newValue = cur.elem();
                            }
                        } else {
                            final IntSetView cachedKeys =
                                    currentRepresentation
                                            .explicitRepresentation
                                            .getCacheView()
                                            .keySet();
                            newValue =
                                    cachedKeys.isEmpty()
                                            ? 0
                                            : cachedKeys.statistics().highestValue() + 1;
                        }
                        literal = LitExprConverter.toLitExpr(newValue, decl.getType());
                        final var extendedModel = MutableValuation.copyOf(model);
                        extendedModel.put(decl, literal);
                        modelToCache = extendedModel;
                    }
                    // Incrementally add negation for the newly found edge
                    solver.add(Neq(currentRepresentation.decl.getRef(), literal));
                    cacheModel(modelToCache);
                    return QueryResult.singleEdge(LitExprConverter.toInt(literal));
                } else {
                    stopEnumeration();
                    if (constraintApplied && !Objects.equals(constraint, True())) {
                        return QueryResult.constrainedFailed();
                    } else {
                        currentRepresentation.explicitRepresentation.setComplete();
                    }
                }
            }
            return QueryResult.failed();
        }

        // TODO osszevonni queryChilddal
        public MddNode moveDown(int assignment) {
            if (queryEdge(assignment)) {
                final MddNode childNode =
                        currentRepresentation.explicitRepresentation.getCacheView().get(assignment);
                Preconditions.checkArgument(
                        childNode.getRepresentation() instanceof MddExpressionRepresentation);
                stack.push(currentRepresentation);
                stopEnumeration();
                setCurrentRepresentation(
                        (MddExpressionRepresentation) childNode.getRepresentation());
                return childNode;
            } else return null;
        }

        //        private void pushNegatedAssignments() {
        //            solver.push();
        //            final var negatedAssignments = new ArrayList<Expr<BoolType>>();
        //            for (var cur =
        // currentRepresentation.explicitRepresentation.getCacheView().cursor();
        //                    cur.moveNext(); ) {
        //                negatedAssignments.add(
        //                        Neq(
        //                                currentRepresentation.decl.getRef(),
        //                                LitExprConverter.toLitExpr(
        //                                        cur.key(),
        // currentRepresentation.decl.getType())));
        //                pushedNegatedAssignments++;
        //            }
        //            solver.add(And(negatedAssignments));
        //        }

        //        private void popNegatedAssignments() {
        //            solver.pop();
        //            pushedNegatedAssignments = 0;
        //        }

        void cacheModel(Valuation valuation) {
            currentRepresentation.cacheModel(valuation);
        }

        private void setCurrentRepresentation(MddExpressionRepresentation representation) {
            this.currentRepresentation = representation;
        }

        @Override
        public void close() {
            if (solver != null) {
                stopEnumeration();
                solverPool.returnSolver(this.solver);
                this.solver = null;
            }
        }

        private static class QueryResult {
            private final QueryResult.Status status;

            private final int key;

            private QueryResult(int key, QueryResult.Status status) {
                this.status = status;
                this.key = key;
            }

            public static QueryResult singleEdge(int key) {
                return new QueryResult(key, QueryResult.Status.SINGLE_EDGE);
            }

            public static QueryResult constrainedFailed() {
                return new QueryResult(-1, Status.CONSTRAINED_FAILED);
            }

            public static QueryResult failed() {
                return new QueryResult(-1, QueryResult.Status.FAILED);
            }

            public static QueryResult defaultEdge() {
                return new QueryResult(-1, QueryResult.Status.DEFAULT_EDGE);
            }

            public int getKey() {
                return key;
            }

            public QueryResult.Status getStatus() {
                return status;
            }

            /**
             * The status of the result. FAILED: no further edges are possible SINGLE_EDGE: a single
             * edge was found DEFAULT_EDGE: the node is a level-skip and has a default value
             */
            public enum Status {
                FAILED,
                SINGLE_EDGE,
                DEFAULT_EDGE,
                CONSTRAINED_FAILED
            }
        }
    }

    private static class Cursor implements RecursiveIntObjCursor<MddNode> {

        // Fields for node enumeration
        private final Traverser traverser;

        // Fields for the recursive cursor structure
        private final Cursor parent;
        private boolean blocked = false;
        private boolean closed = false;

        // Common cursor fields
        private int index;
        private int key;
        private MddNode value;
        private boolean initialized = false;

        // Fields for constrained cursors
        private boolean constrainedFailed = false;

        public Cursor(final Cursor parent, final Traverser traverser) {
            this.parent = parent;
            this.traverser = traverser;
            this.index = -1;
            this.key = -1;
            this.value = null;
        }

        private static class Terminal implements RecursiveIntObjCursor<MddNode> {

            private final Cursor parent;

            private Terminal(final Cursor parent) {
                this.parent = parent;
            }

            @Override
            public boolean moveTo(int i) {
                return false;
            }

            @Override
            public void close() {
                parent.unblock();
            }

            // TODO: exception
            @Override
            public int key() {
                return 0;
            }

            // TODO: exception
            @Override
            public MddNode value() {
                return null;
            }

            @Override
            public boolean moveNext() {
                return false;
            }
        }

        @Override
        public boolean moveTo(int key) {
            Preconditions.checkState(
                    !blocked, "Cursor can't be moved until its children are disposed of");
            Preconditions.checkState(!closed, "Cursor can't be moved if it was closed");

            var currentRepresentation = traverser.currentRepresentation;
            if (currentRepresentation.explicitRepresentation.getCacheView().containsKey(key)
                    || !currentRepresentation.explicitRepresentation.isComplete()
                            && traverser.queryEdge(key)) {
                this.key = key;
                this.value = currentRepresentation.get(key);
                this.initialized = true;
                return true;
            }
            return false;
        }

        @Override
        public RecursiveIntObjCursor<MddNode> valueCursor() {
            Preconditions.checkState(!blocked, "Can't provide value cursor for blocked cursor");
            Preconditions.checkState(!closed, "Can't provide value cursor for closed cursor");

            this.blocked = true;
            final MddNode childNode = this.traverser.peekDown(key);
            if (childNode.isTerminal()) {
                return new Terminal(this);
            } else {
                this.traverser.moveDown(key);
                return new Cursor(this, traverser);
            }
        }

        @Override
        public int key() {
            Preconditions.checkState(initialized, "Cursor is not initialized");
            return key;
        }

        @Override
        public MddNode value() {
            Preconditions.checkState(initialized, "Cursor is not initialized");
            return value;
        }

        @Override
        public boolean moveNext() {
            Preconditions.checkState(
                    !blocked, "Cursor can't be moved until its children are not closed");
            Preconditions.checkState(!closed, "Cursor can't be moved if it was closed");

            var currentRepresentation = traverser.currentRepresentation;
            if (index < currentRepresentation.explicitRepresentation.getSize() - 1) {
                index++;
                key = currentRepresentation.explicitRepresentation.getEdge(index);
                value = currentRepresentation.explicitRepresentation.getCacheView().get(key);
                initialized = true;
                currentRepresentation.explicitRepresentation.markVisited(key);
                return true;
            } else if (!currentRepresentation.explicitRepresentation.isComplete()
                    && !constrainedFailed) {
                final MddExpressionRepresentation.Traverser.QueryResult queryResult =
                        traverser.queryEdge();
                if (queryResult.getStatus()
                        == MddExpressionRepresentation.Traverser.QueryResult.Status.SINGLE_EDGE) {
                    index++;
                    key = queryResult.getKey();
                    value = currentRepresentation.explicitRepresentation.getCacheView().get(key);
                    initialized = true;
                    currentRepresentation.explicitRepresentation.markVisited(key);
                    return true;
                } else if (queryResult.getStatus()
                        == Traverser.QueryResult.Status.CONSTRAINED_FAILED) {
                    this.constrainedFailed = true;
                }
            }
            traverser.close();
            return false;
        }

        @Override
        public void close() {
            this.closed = true;
            if (parent != null) {
                traverser.moveUp();
                parent.unblock();
            } else {
                traverser.close();
            }
        }

        private void unblock() {
            this.blocked = false;
        }
    }
}
