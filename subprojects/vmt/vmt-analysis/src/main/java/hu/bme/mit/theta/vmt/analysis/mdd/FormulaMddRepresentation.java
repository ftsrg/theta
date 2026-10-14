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
package hu.bme.mit.theta.vmt.analysis.mdd;

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
import hu.bme.mit.theta.common.GrowingIntArray;
import hu.bme.mit.theta.common.exception.NotSolvableException;
import java.io.Closeable;
import java.util.*;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;

/**
 * The JavaSMT counterpart of {@code MddExpressionRepresentation}: an MDD node given by a formula
 * over the level's variable and the variables below it. Edges are found lazily with the solver and
 * cached; once all are known the node is complete.
 */
public final class FormulaMddRepresentation implements RecursiveIntObjMapView<MddNode> {

    private final BooleanFormula expr;
    private final FormulaVar decl;
    private final MddVariable mddVariable;

    private Traverser lazyTraverser;
    private final ExplicitRepresentation explicitRepresentation;

    private final FormulaMddContext ctx;
    private final boolean transExpr;
    public static final MddGraph.Key<LookAhead> LOOK_AHEAD = new MddGraph.Key<>("formulaLookAhead");

    /** How a constraining MDD is turned into a formula that guides edge enumeration. */
    public enum LookAhead {
        NONE {
            @Override
            public BooleanFormula toConstraint(MddHandle handle, FormulaMddContext ctx) {
                return ctx.getBooleanFormulaManager().makeTrue();
            }
        },
        VARIABLE_LEVEL {
            @Override
            public BooleanFormula toConstraint(MddHandle handle, FormulaMddContext ctx) {
                return FormulaBoundsConstraint.of(handle, ctx);
            }
        };

        public abstract BooleanFormula toConstraint(MddHandle handle, FormulaMddContext ctx);
    }

    private FormulaMddRepresentation(
            final BooleanFormula expr,
            final FormulaVar decl,
            final MddVariable mddVariable,
            final FormulaMddContext ctx,
            final boolean transExpr) {
        this.expr = expr;
        this.decl = decl;
        this.mddVariable = mddVariable;
        this.ctx = ctx;
        this.explicitRepresentation = new ExplicitRepresentation();
        this.transExpr = transExpr;
    }

    /** Read-only view of the explored structure. */
    public Explored explored() {
        return explicitRepresentation;
    }

    public static FormulaMddRepresentation of(
            final BooleanFormula expr,
            final FormulaVar decl,
            final MddVariable mddVariable,
            final FormulaMddContext ctx,
            final boolean transExpr) {
        return new FormulaMddRepresentation(expr, decl, mddVariable, ctx, transExpr);
    }

    public static FormulaMddRepresentation of(
            final BooleanFormula expr,
            final FormulaVar decl,
            final MddVariable mddVariable,
            final FormulaMddContext ctx,
            final boolean transExpr,
            final Map<String, Object> satModel) {
        final var repr = new FormulaMddRepresentation(expr, decl, mddVariable, ctx, transExpr);
        if (satModel != null) {
            repr.getLazyTraverser().cacheModel(satModel);
        }
        return repr;
    }

    public static FormulaMddRepresentation ofDefault(
            final BooleanFormula expr,
            final FormulaVar decl,
            final MddVariable mddVariable,
            final FormulaMddContext ctx,
            final MddNode defaultValue,
            final boolean transExpr) {
        final FormulaMddRepresentation representation =
                new FormulaMddRepresentation(expr, decl, mddVariable, ctx, transExpr);
        representation.explicitRepresentation.cacheDefault(defaultValue);
        representation.explicitRepresentation.setComplete();
        return representation;
    }

    public static FormulaMddRepresentation ofDetermined(
            final BooleanFormula expr,
            final FormulaVar decl,
            final MddVariable mddVariable,
            final FormulaMddContext ctx,
            final int key,
            final MddNode childNode,
            final boolean transExpr) {
        final FormulaMddRepresentation representation =
                new FormulaMddRepresentation(expr, decl, mddVariable, ctx, transExpr);
        if (!mddVariable.isNullOrZero(childNode)) {
            representation.explicitRepresentation.cacheNode(key, childNode);
        }
        representation.explicitRepresentation.setComplete();
        return representation;
    }

    public BooleanFormula getExpr() {
        return expr;
    }

    public FormulaVar getDecl() {
        return decl;
    }

    public MddVariable getMddVariable() {
        return mddVariable;
    }

    private Traverser getLazyTraverser() {
        if (lazyTraverser == null) lazyTraverser = Traverser.create(this, ctx);
        return lazyTraverser;
    }

    /** Caches the edges along {@code model}, a model of {@link #getExpr()}. */
    public void cacheModel(Map<String, Object> model) {
        final MddNode existingDefault = explicitRepresentation.getCacheView().defaultValue();
        final FormulaMddRepresentation child;
        if (existingDefault != null) {
            child = childRepresentation(existingDefault);
        } else {
            final Object value = model.get(decl.name());
            child = value != null ? cacheChild(ctx.toKey(value, decl), true) : cacheChild(0, false);
        }
        if (child != null) child.cacheModel(model);
    }

    private FormulaMddRepresentation cacheChild(int key, boolean cacheEdge) {
        MddNode childNode = cacheEdge ? explicitRepresentation.getCacheView().get(key) : null;
        if (childNode == null) {
            final BooleanFormula substituted =
                    cacheEdge
                            ? FormulaMddTemplate.substituteAndSimplify(
                                    expr,
                                    decl,
                                    ctx.toValueFormula(key, decl),
                                    ctx,
                                    mddVariable.getMddGraph())
                            : expr;
            if (mddVariable.getLower().isPresent()) {
                childNode =
                        mddVariable
                                .getLower()
                                .get()
                                .checkInNode(
                                        FormulaMddTemplate.ofKnownSat(substituted, ctx, transExpr));
            } else {
                childNode = graph().getNodeFor(ctx.getBooleanFormulaManager().makeTrue());
            }
            if (cacheEdge
                    && !explicitRepresentation.isComplete()
                    && explicitRepresentation.getCacheView().defaultValue() == null
                    && !mddVariable.isNullOrZero(childNode)) {
                cacheExploredEdge(key, childNode);
                completeIfBoolFullyCached();
            }
        }
        return childRepresentation(childNode);
    }

    /** The expression node a child resolves to, unwrapping identity levels; null at a terminal. */
    private static FormulaMddRepresentation childRepresentation(MddNode childNode) {
        if (childNode.isTerminal()) return null;
        var repr = childNode.getRepresentation();
        while (repr instanceof IdentityRepresentation) {
            final MddNode cont = ((IdentityRepresentation) repr).getContinuation();
            if (cont.isTerminal()) return null;
            repr = cont.getRepresentation();
        }
        return (FormulaMddRepresentation) repr;
    }

    private void cacheExploredEdge(final int key, final MddNode childNode) {
        if (explicitRepresentation.getSize() >= ctx.getEdgeLimit()) {
            throw new NotSolvableException();
        }
        explicitRepresentation.cacheNode(key, childNode);
    }

    @SuppressWarnings("unchecked")
    private MddGraph<BooleanFormula> graph() {
        return (MddGraph<BooleanFormula>) mddVariable.getMddGraph();
    }

    /** A bool decl has exactly the keys 0 and 1, so deciding both makes the node complete. */
    public void completeIfBoolFullyCached() {
        if (decl.type().isBooleanType()
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
            return cached;
        }
        if (explicitRepresentation.isNegativelyCached(key)) return null;

        final Formula value = ctx.toValueFormula(key, decl);
        if (value == null) {
            explicitRepresentation.cacheNegative(key);
            completeIfBoolFullyCached();
            return null;
        }

        final BooleanFormula simplifiedExpr =
                FormulaMddTemplate.substituteAndSimplify(
                        expr, decl, value, ctx, mddVariable.getMddGraph());

        final MddNode childNode;
        if (mddVariable.getLower().isPresent()) {
            final FormulaMddTemplate template =
                    FormulaMddTemplate.of(simplifiedExpr, ctx, transExpr);
            childNode = mddVariable.getLower().get().checkInNode(template);
        } else {
            final BooleanFormula top = ctx.getBooleanFormulaManager().makeTrue();
            if (ctx.isFalse(simplifiedExpr)) {
                childNode = null;
            } else if (ctx.isTrue(simplifiedExpr)) {
                childNode = graph().getNodeFor(top);
            } else {
                final FormulaProver solver = ctx.getProverPool().requestProver();
                try {
                    solver.push();
                    solver.add(simplifiedExpr);
                    childNode = solver.check() ? graph().getNodeFor(top) : null;
                    solver.pop();
                } finally {
                    ctx.getProverPool().returnProver(solver);
                }
            }
        }
        if (!mddVariable.isNullOrZero(childNode)) {
            cacheExploredEdge(key, childNode);
        } else {
            // remember the absence, so the key is not queried again
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
        return new Cursor(null, Traverser.create(this, ctx));
    }

    @Override
    public RecursiveIntObjCursor<? extends MddNode> cursor(RecursiveIntObjMapView<?> constraint) {
        Preconditions.checkArgument(constraint instanceof MddHandle);
        final MddHandle mddHandle = (MddHandle) constraint;

        var strategy = mddVariable.getMddGraph().getAttribute(LOOK_AHEAD);
        if (strategy == null) {
            strategy = LookAhead.VARIABLE_LEVEL;
        }
        final var constraintExpr = strategy.toConstraint(mddHandle, ctx);

        return new Cursor(null, Traverser.create(this, constraintExpr, ctx));
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
        if (that instanceof FormulaMddRepresentation) {
            return Objects.equals(mddVariable, ((FormulaMddRepresentation) that).mddVariable)
                    && Objects.equals(decl, ((FormulaMddRepresentation) that).decl)
                    && (Objects.equals(expr, ((FormulaMddRepresentation) that).expr)
                            || semanticEquals(that));
        }
        if (that instanceof MddNode) {
            return this.equals(((MddNode) that).getRepresentation());
        }
        return false;
    }

    private boolean semanticEquals(Object that) {

        if (that instanceof FormulaMddRepresentation thatRepresentation) {
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

    /** What exploration has established about a node so far: its cached edges and completeness. */
    public interface Explored {
        IntObjMapView<MddNode> knownEdges();

        boolean isComplete();
    }

    static class ExplicitRepresentation implements Explored {
        private final HashIntObjMap<MddNode> cache;
        private final GrowingIntArray edgeOrdering;
        private final HashIntSet negativeCache;
        private MddNode defaultValue;
        private boolean complete;

        public ExplicitRepresentation() {
            this.cache = HashIntObjMaps.newUpdatableMap();
            this.edgeOrdering = new GrowingIntArray(100, 100);
            this.negativeCache = HashIntSets.newUpdatableSet();
            this.defaultValue = null;
            this.complete = false;
        }

        void cacheNode(int key, MddNode node) {
            Preconditions.checkState(!complete);
            Preconditions.checkState(defaultValue == null);
            this.cache.put(key, node);
            this.edgeOrdering.add(key);
        }

        void cacheNegative(int key) {
            negativeCache.add(key);
        }

        public boolean isNegativelyCached(int key) {
            return negativeCache.contains(key);
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

        public int getEdge(int index) {
            return edgeOrdering.get(index);
        }

        public int getSize() {
            return edgeOrdering.getSize();
        }
    }

    private static class Traverser implements Closeable {

        private FormulaMddRepresentation currentRepresentation;
        private final BooleanFormula constraint;
        private boolean constraintApplied;

        private final FormulaMddContext ctx;
        private FormulaProver solver;

        private final Stack<FormulaMddRepresentation> stack;

        // Tracks whether the solver has a persistent push level with the
        // base expression + accumulated negations for the current level
        private boolean enumerationActive = false;

        private Traverser(
                FormulaMddRepresentation rootRepresentation,
                BooleanFormula constraint,
                FormulaMddContext ctx) {
            this.ctx = ctx;
            this.stack = new Stack<>();
            this.constraint = constraint;
            this.currentRepresentation = rootRepresentation;
            this.constraintApplied = false;
        }

        public static Traverser create(
                FormulaMddRepresentation rootRepresentation,
                BooleanFormula constraint,
                FormulaMddContext ctx) {
            return new Traverser(rootRepresentation, constraint, ctx);
        }

        public static Traverser create(
                FormulaMddRepresentation rootRepresentation, FormulaMddContext ctx) {
            return new Traverser(
                    rootRepresentation, ctx.getBooleanFormulaManager().makeTrue(), ctx);
        }

        private void stopEnumeration() {
            if (enumerationActive && solver != null) {
                solver.pop();
                enumerationActive = false;
            }
            releaseSolver();
        }

        // hold the solver only while an enumeration keeps state in it
        private void releaseSolver() {
            if (solver != null && !enumerationActive) {
                ctx.getProverPool().returnProver(solver);
                solver = null;
            }
        }

        public FormulaMddRepresentation moveUp() {
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
                return true;
            }
            if (currentRepresentation.explicitRepresentation.getCacheView().defaultValue() != null)
                return true;
            if (currentRepresentation.explicitRepresentation.isNegativelyCached(assignment))
                return false;
            if (!currentRepresentation.explicitRepresentation.isComplete()) {
                if (solver == null) solver = ctx.getProverPool().requestProver();

                final boolean sat;
                final Map<String, Object> model;
                final Formula value = ctx.toValueFormula(assignment, currentRepresentation.decl);
                if (value == null) {
                    releaseSolver();
                    currentRepresentation.explicitRepresentation.cacheNegative(assignment);
                    currentRepresentation.completeIfBoolFullyCached();
                    return false;
                }
                solver.push();
                try {
                    if (!enumerationActive) {
                        solver.add(currentRepresentation.expr);
                    }
                    solver.add(ctx.equal(currentRepresentation.decl, value));
                    sat = solver.check();
                    model = sat ? ctx.model(solver) : null;
                } finally {
                    solver.pop();
                }
                releaseSolver();
                if (sat) {
                    cacheModel(model);
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

                if (solver == null) solver = ctx.getProverPool().requestProver();

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
                                ctx.getBooleanFormulaManager()
                                        .not(
                                                ctx.equal(
                                                        currentRepresentation.decl,
                                                        ctx.toValueFormula(
                                                                cur.key(),
                                                                currentRepresentation.decl))));
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

                final boolean sat = solver.check();
                final Map<String, Object> model = sat ? ctx.model(solver) : null;

                if (sat) {
                    final FormulaVar decl = currentRepresentation.decl;
                    final Object modelValue = model.get(decl.name());

                    final Object literal;
                    final Map<String, Object> modelToCache;
                    if (modelValue != null) {
                        literal = modelValue;
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
                        literal = ctx.toValue(newValue, decl);
                        final Map<String, Object> extendedModel = new HashMap<>(model);
                        extendedModel.put(decl.name(), literal);
                        modelToCache = extendedModel;
                    }
                    cacheModel(modelToCache);
                    final int key = ctx.toKey(literal, decl);
                    if (currentRepresentation.explicitRepresentation.isComplete()
                            && !currentRepresentation
                                    .explicitRepresentation
                                    .getCacheView()
                                    .containsKey(key)) {
                        // the edge limit closed the level instead of taking this edge
                        stopEnumeration();
                        return QueryResult.failed();
                    }
                    // Incrementally add negation for the newly found edge
                    solver.add(
                            ctx.getBooleanFormulaManager()
                                    .not(
                                            ctx.equal(
                                                    currentRepresentation.decl,
                                                    ctx.toValueFormula(key, decl))));
                    return QueryResult.singleEdge(key);
                } else {
                    stopEnumeration();
                    if (constraintApplied && !ctx.isTrue(constraint)) {
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
                        childNode.getRepresentation() instanceof FormulaMddRepresentation);
                stack.push(currentRepresentation);
                stopEnumeration();
                setCurrentRepresentation((FormulaMddRepresentation) childNode.getRepresentation());
                return childNode;
            } else return null;
        }

        void cacheModel(Map<String, Object> valuation) {
            currentRepresentation.cacheModel(valuation);
        }

        private void setCurrentRepresentation(FormulaMddRepresentation representation) {
            this.currentRepresentation = representation;
        }

        @Override
        public void close() {
            stopEnumeration();
            releaseSolver();
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
                return true;
            } else if (!currentRepresentation.explicitRepresentation.isComplete()
                    && !constrainedFailed) {
                final FormulaMddRepresentation.Traverser.QueryResult queryResult =
                        traverser.queryEdge();
                if (queryResult.getStatus()
                        == FormulaMddRepresentation.Traverser.QueryResult.Status.SINGLE_EDGE) {
                    index++;
                    key = queryResult.getKey();
                    value = currentRepresentation.explicitRepresentation.getCacheView().get(key);
                    initialized = true;
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
