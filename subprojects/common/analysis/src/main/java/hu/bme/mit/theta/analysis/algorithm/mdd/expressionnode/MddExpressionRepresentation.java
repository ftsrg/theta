/*
 *  Copyright 2025-2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.hash.HashIntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import hu.bme.mit.delta.collections.*;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation;
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

    private MddExpressionRepresentation(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final MddVariable mddVariable,
            final SolverPool solverPool,
            final boolean transExpr) {
        this.expr = expr;
        this.decl = decl;
        this.mddVariable = mddVariable;
        this.solverPool = solverPool;
        this.explicitRepresentation = new ExplicitRepresentation();
        this.transExpr = transExpr;
    }

    // TODO only for debugging
    public ExplicitRepresentation getExplicitRepresentation() {
        return explicitRepresentation;
    }

    public static MddExpressionRepresentation of(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final MddVariable mddVariable,
            final SolverPool solverPool,
            final boolean transExpr) {
        return new MddExpressionRepresentation(expr, decl, mddVariable, solverPool, transExpr);
    }

    public static MddExpressionRepresentation ofDefault(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final MddVariable mddVariable,
            final SolverPool solverPool,
            final MddNode defaultValue,
            final boolean transExpr) {
        final MddExpressionRepresentation representation =
                new MddExpressionRepresentation(expr, decl, mddVariable, solverPool, transExpr);
        representation.explicitRepresentation.cacheDefault(defaultValue);
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
        if (cached != null || this.explicitRepresentation.isComplete()) return cached;
        // TODO: this way null values are never cached and have to be recomputed every time

        final MutableValuation val = new MutableValuation();
        final LitExpr<?> litExpr = LitExprConverter.toLitExpr(key, decl.getType());
        if (litExpr.isInvalid()) {
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
                    MddExpressionTemplate.of(simplifiedExpr, o -> (Decl) o, solverPool, transExpr);
            childNode = mddVariable.getLower().get().checkInNode(template);
        } else {
            final Expr<BoolType> canonizedExpr =
                    ExprUtils.canonize(ExprUtils.simplify(simplifiedExpr));
            MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();

            if (canonizedExpr instanceof FalseExpr) {
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
        if (!mddVariable.isNullOrZero(childNode)) explicitRepresentation.cacheNode(key, childNode);
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

        //        final var concreteExpr = MddToExprUtilKt.toExprNodeLevel(mddHandle);
        final var abstractExpr = MddToExprUtilKt.toApproximationExprVariableLevel(mddHandle);

        return new Cursor(null, Traverser.create(this, abstractExpr, solverPool));
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

    public static class ExplicitRepresentation {
        private final HashIntObjMap<MddNode> cache;
        private final GrowingIntArray edgeOrdering;
        private MddNode defaultValue;
        private boolean complete;

        public ExplicitRepresentation() {
            this.cache = HashIntObjMaps.newUpdatableMap();
            this.edgeOrdering = new GrowingIntArray(100, 100);
            this.defaultValue = null;
            this.complete = false;
        }

        public void cacheNode(int key, MddNode node) {
            Preconditions.checkState(!complete);
            Preconditions.checkState(defaultValue == null);
            if (this.cache.size() > 1000) {
                throw new NotSolvableException();
            }
            this.cache.put(key, node);
            this.edgeOrdering.add(key);
        }

        public void cacheDefault(MddNode defaultValue) {
            Preconditions.checkState(!complete);
            this.defaultValue = defaultValue;
        }

        public void setComplete() {
            this.complete = true;
        }

        public IntObjMapView<MddNode> getCacheView() {
            return IntObjMapView.of(cache, defaultValue);
        }

        public boolean isComplete() {
            return complete;
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

        public MddExpressionRepresentation moveUp() {
            //            throw new UnsupportedOperationException();
            Preconditions.checkState(stack.size() > 0);
            setCurrentRepresentation(stack.pop());
            return currentRepresentation;
        }

        public boolean queryEdge(int assignment) {
            if (currentRepresentation
                            .explicitRepresentation
                            .getCacheView()
                            .keySet()
                            .contains(assignment)
                    || currentRepresentation.explicitRepresentation.getCacheView().defaultValue()
                            != null) return true;
            else if (!currentRepresentation.explicitRepresentation.isComplete()) {

                if (solver == null) solver = solverPool.requestSolver();

                final SolverStatus status;
                final Valuation model;
                final LitExpr<?> litExpr =
                        LitExprConverter.toLitExpr(
                                assignment, currentRepresentation.decl.getType());
                try (WithPushPop wpp = new WithPushPop(solver)) {
                    solver.add(currentRepresentation.expr);
                    //                    solver.add(constraint);
                    solver.add(Eq(currentRepresentation.decl.getRef(), litExpr));
                    solver.check();
                    status = solver.getStatus();
                    model = status.isSat() ? solver.getModel() : null;
                }
                Preconditions.checkNotNull(status);
                if (status.isSat()) {
                    cacheModel(model);
                    return true;
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

                final Valuation model;
                final SolverStatus status;
                try (var wpp = new WithPushPop(solver)) {

                    solver.add(currentRepresentation.expr);
                    if (currentRepresentation.explicitRepresentation.getCacheView().size() >= 0) {
                        solver.add(constraint);
                        constraintApplied = true;
                    }
                    final var negatedAssignments = new ArrayList<Expr<BoolType>>();
                    for (var cur =
                                    currentRepresentation
                                            .explicitRepresentation
                                            .getCacheView()
                                            .cursor();
                            cur.moveNext(); ) {
                        negatedAssignments.add(
                                Neq(
                                        currentRepresentation.decl.getRef(),
                                        LitExprConverter.toLitExpr(
                                                cur.key(), currentRepresentation.decl.getType())));
                    }
                    solver.add(And(negatedAssignments));

                    solver.check();
                    status = solver.getStatus();
                    model = status.isSat() ? solver.getModel() : null;
                }

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
                                currentRepresentation.explicitRepresentation.setComplete();
                                return QueryResult.failed();
                            } else {
                                final var cur = remaining.cursor();
                                Preconditions.checkState(cur.moveNext());
                                newValue = cur.elem();
                            }
                        } else {
                            // only visited once per node, because of the negated assignment that is
                            // pushed to the solver
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
                    cacheModel(modelToCache);
                    return QueryResult.singleEdge(LitExprConverter.toInt(literal));
                } else {
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

        private void cacheModel(Valuation valuation) {
            MddExpressionRepresentation representation = currentRepresentation;

            while (true) {

                final MddNode childNode;
                if (representation.explicitRepresentation.getCacheView().defaultValue() != null) {

                    childNode = representation.explicitRepresentation.getCacheView().defaultValue();

                } else {

                    // Substitute literal if available
                    final Optional<? extends LitExpr<?>> literal =
                            valuation.eval(representation.getDecl());
                    final Expr<BoolType> substitutedExpr;
                    if (literal.isPresent()) {
                        substitutedExpr =
                                ExprUtils.simplify(
                                        representation.expr,
                                        ImmutableValuation.builder()
                                                .put(representation.getDecl(), literal.get())
                                                .build());
                    } else {
                        substitutedExpr = representation.expr;
                    }

                    if (literal.isPresent()
                            && representation
                                    .explicitRepresentation
                                    .getCacheView()
                                    .containsKey(LitExprConverter.toInt(literal.get()))) {
                        // Return cached if available
                        childNode =
                                representation
                                        .explicitRepresentation
                                        .getCacheView()
                                        .get(LitExprConverter.toInt(literal.get()));
                    } else {
                        final Optional<? extends MddVariable> lower =
                                representation.mddVariable.getLower();
                        if (lower.isPresent()) {
                            final MddExpressionTemplate template =
                                    MddExpressionTemplate.ofKnownSat(
                                            substitutedExpr,
                                            o -> (Decl) o,
                                            representation.solverPool,
                                            currentRepresentation.transExpr);
                            childNode = lower.get().checkInNode(template);
                        } else {
                            final Expr<BoolType> canonizedExpr =
                                    ExprUtils.canonize(substitutedExpr);
                            MddGraph<Expr> mddGraph =
                                    (MddGraph<Expr>) representation.mddVariable.getMddGraph();
                            assert !(canonizedExpr instanceof FalseExpr);
                            // TODO replace this with canonizedExpr if remainder expression is
                            // needed
                            childNode = mddGraph.getNodeFor(True());
                        }

                        assert !representation.mddVariable.isNullOrZero(childNode)
                                : "This would mean the model returned by the solver is incorrect";
                        if (literal.isPresent())
                            representation.explicitRepresentation.cacheNode(
                                    LitExprConverter.toInt(literal.get()), childNode);
                        // TODO update domainSize
                    }
                }

                if (childNode.isTerminal()) return;

                // Preconditions.checkArgument(childNode.getRepresentation() instanceof
                // MddExpressionRepresentation);
                // TODO assert
                var nextRepr = childNode.getRepresentation();
                while (nextRepr instanceof IdentityRepresentation identity) {
                    var cont = identity.getContinuation();
                    if (cont.isTerminal()) return;
                    nextRepr = cont.getRepresentation();
                }
                representation = (MddExpressionRepresentation) nextRepr;
            }
        }

        private void setCurrentRepresentation(MddExpressionRepresentation representation) {
            this.currentRepresentation = representation;
        }

        @Override
        public void close() {
            if (solver != null) {
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
