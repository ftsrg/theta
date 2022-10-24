package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.hash.HashIntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.common.GrowingIntArray;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.Optional;
import java.util.Stack;
import java.util.function.Supplier;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;

public class MddExpressionRepresentation implements RecursiveIntObjMapView<MddNode> {

    private final Expr<BoolType> expr;
    private final VarDecl<?> decl;
    private final MddVariable mddVariable;

    private Traverser lazyTraverser;
    private final ExplicitRepresentation explicitRepresentation;

    private final Supplier<Solver> solverSupplier;

    private MddExpressionRepresentation(final Expr<BoolType> expr, final VarDecl<?> decl, final MddVariable mddVariable, final Supplier<Solver> solverSupplier) {
        this.expr = expr;
        this.decl = decl;
        this.mddVariable = mddVariable;
        this.solverSupplier = solverSupplier;
        this.explicitRepresentation = new ExplicitRepresentation();
    }

    public static MddExpressionRepresentation of(final Expr<BoolType> expr, final VarDecl<?> decl, final MddVariable mddVariable, final Supplier<Solver> solverSupplier) {
        return new MddExpressionRepresentation(expr, decl, mddVariable, solverSupplier);
    }

    public static MddExpressionRepresentation ofDefault(final Expr<BoolType> expr, final VarDecl<?> decl, final MddVariable mddVariable, final Supplier<Solver> solverSupplier, final MddNode defaultValue) {
        final MddExpressionRepresentation representation = new MddExpressionRepresentation(expr, decl, mddVariable, solverSupplier);
        representation.explicitRepresentation.cacheDefault(defaultValue);
        representation.explicitRepresentation.setComplete();
        return representation;
    }

    public Expr<BoolType> getExpr() {
        return expr;
    }

    public VarDecl<?> getDecl() {
        return decl;
    }

    public MddVariable getMddVariable() {
        return mddVariable;
    }

    private Traverser getLazyTraverser() {
        if (lazyTraverser == null) lazyTraverser = new Traverser(this, solverSupplier);
        return lazyTraverser;
    }

    @Override
    public boolean isEmpty() {
        if (!explicitRepresentation.getCacheView().isEmpty()) return false;
        getLazyTraverser().queryEdge();
        return explicitRepresentation.getCacheView().isEmpty();
    }

    @Override
    public boolean isProcedural() {
        return true;
    }

    @Override
    public boolean containsKey(int key) {
        return getLazyTraverser().queryEdge(key);
    }

    @Override
    public MddNode get(int key) {
        getLazyTraverser().queryEdge(key);
        // Traverser is responsible for caching
        return explicitRepresentation.getCacheView().get(key);
    }

    @Override
    public MddNode defaultValue() {
        return explicitRepresentation.getCacheView().defaultValue();
    }

    @Override
    public RecursiveIntObjCursor<? extends MddNode> cursor() {
        // TODO temporary solution, replace with proper recursive cursor
        throw new UnsupportedOperationException("Not implemented yet");
    }

    @Override
    public int size() {
        if (explicitRepresentation.isComplete()) return explicitRepresentation.getCacheView().size();
        return -1;
    }

    private static class ExplicitRepresentation {
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

    private static class Traverser {

        private MddExpressionRepresentation currentRepresentation;

        private final Solver solver;

        private final Stack<MddExpressionRepresentation> stack;
        private int pushedNegatedAssignments = 0;

        public Traverser(MddExpressionRepresentation rootRepresentation, Supplier<Solver> solverSupplier) {
            this.solver = solverSupplier.get();
            this.stack = new Stack<>();

            setCurrentRepresentation(Preconditions.checkNotNull(rootRepresentation));
            solver.add(rootRepresentation.expr);
            solver.push();
        }

        public MddExpressionRepresentation moveUp() {
            Preconditions.checkState(stack.size() > 0);
            popNegatedAssignments();
            solver.pop(); // pop assignment that brought us here
            setCurrentRepresentation(stack.pop());
            return currentRepresentation;
        }

        public boolean queryEdge(int assignment) {
            if (currentRepresentation.explicitRepresentation.getCacheView().keySet().contains(assignment) || currentRepresentation.explicitRepresentation.getCacheView().defaultValue() != null)
                return true;
            else if (!currentRepresentation.explicitRepresentation.isComplete()) {
                final SolverStatus status;
                final Valuation model;
                final LitExpr<?> litExpr = LitExprConverter.toLitExpr(assignment, currentRepresentation.decl.getType());
                try (WithPushPop wpp = new WithPushPop(solver)) {
                    solver.add(Eq(currentRepresentation.decl.getRef(), litExpr));
                    solver.check();
                    status = solver.getStatus();
                    model = status.isSat() ? solver.getModel() : null;
                }
                Preconditions.checkNotNull(status);
                if (status.isSat()) {
                    cacheModel(model);
                    solver.add(Neq(currentRepresentation.decl.getRef(), litExpr));
                    pushedNegatedAssignments++;
                    return true;
                }
            }
            return false;
        }

        public MddNode peakDown(int assignment) {
            queryEdge(assignment);
            return currentRepresentation.explicitRepresentation.getCacheView().get(assignment);
        }

        public QueryResult queryEdge() {
            if (!currentRepresentation.explicitRepresentation.isComplete()) {
                if (pushedNegatedAssignments != currentRepresentation.explicitRepresentation.getCacheView().keySet().size()) {
                    popNegatedAssignments();
                    pushNegatedAssignments();
                }
                solver.check();
                if (solver.getStatus().isSat()) {
                    final Valuation model = solver.getModel();
                    final VarDecl<?> decl = currentRepresentation.decl;
                    final Optional<? extends LitExpr<?>> optionalLitExpr = model.eval(decl);

                    final LitExpr<?> literal;
                    final Valuation modelToCache;
                    if (optionalLitExpr.isPresent()) {
                        literal = optionalLitExpr.get();
                        modelToCache = model;
                    } else {
                        final int newValue;
                        if (currentRepresentation.mddVariable.isBounded()) {
                            final IntSetView domain = IntSetView.range(0, currentRepresentation.mddVariable.getDomainSize());
                            final IntSetView remaining = domain.minus(currentRepresentation.explicitRepresentation.getCacheView().keySet());
                            if (remaining.isEmpty()) {
                                currentRepresentation.explicitRepresentation.setComplete();
                                return QueryResult.failed();
                            } else {
                                final var cur = remaining.cursor();
                                Preconditions.checkState(cur.moveNext());
                                newValue = cur.elem();
                            }
                        } else {
                            // only visited once per node, because of the negated assignment that is pushed to the solver
                            final IntSetView cachedKeys = currentRepresentation.explicitRepresentation.getCacheView().keySet();
                            newValue = cachedKeys.isEmpty() ? 0 : cachedKeys.statistics().highestValue() + 1;
                        }
                        literal = LitExprConverter.toLitExpr(newValue, decl.getType());
                        final var extendedModel = MutableValuation.copyOf(model);
                        extendedModel.put(decl, literal);
                        modelToCache = extendedModel;
                    }

                    solver.add(Neq(decl.getRef(), literal));
                    pushedNegatedAssignments++;
                    cacheModel(modelToCache);
                    return QueryResult.singleEdge(LitExprConverter.toInt(literal));
                } else {
                    currentRepresentation.explicitRepresentation.setComplete();
                }
            }
            return QueryResult.failed();
        }

        // TODO összevonni queryChilddal
        public MddNode moveDown(int assignment) {
            if (queryEdge(assignment)) {
                popNegatedAssignments();
                solver.push();
                solver.add(Eq(currentRepresentation.decl.getRef(), LitExprConverter.toLitExpr(assignment, currentRepresentation.decl.getType())));
                stack.push(currentRepresentation);
                final MddNode childNode = currentRepresentation.explicitRepresentation.getCacheView().get(assignment);
                Preconditions.checkArgument(childNode.getRepresentation() instanceof MddExpressionRepresentation);
                setCurrentRepresentation((MddExpressionRepresentation) childNode.getRepresentation());
                return childNode;
            } else return null;
        }

        private void pushNegatedAssignments() {
            solver.push();
            for (var cur = currentRepresentation.explicitRepresentation.getCacheView().cursor(); cur.moveNext(); ) {
                solver.add(Neq(currentRepresentation.decl.getRef(), LitExprConverter.toLitExpr(cur.key(), currentRepresentation.decl.getType())));
                pushedNegatedAssignments++;
            }
        }

        private void popNegatedAssignments() {
            solver.pop();
            pushedNegatedAssignments = 0;
        }

        private void cacheModel(Valuation valuation) {
            MddExpressionRepresentation representation = currentRepresentation;
            Expr<?> expr = representation.expr;
            MddVariable variable = currentRepresentation.mddVariable;

            while (variable != null) {

                final Optional<? extends MddVariable> lower = variable.getLower();
                final ConstDecl<?> decl = variable.getTraceInfo(ConstDecl.class);
                final Optional<? extends LitExpr<?>> literal = valuation.eval(decl);

                final MddNode childNode;
                if (currentRepresentation.explicitRepresentation.getCacheView().defaultValue() != null) {
                    childNode = currentRepresentation.explicitRepresentation.getCacheView().defaultValue();
                } else {
                    final LitExpr<?> literalToCache;
                    if (literal.isPresent()) {
                        literalToCache = literal.get();
                    } else {
                        final int newValue;
                        if (currentRepresentation.mddVariable.isBounded()) {
                            final IntSetView domain = IntSetView.range(0, currentRepresentation.mddVariable.getDomainSize());
                            final IntSetView remaining = domain.minus(currentRepresentation.explicitRepresentation.getCacheView().keySet());
                            if (remaining.isEmpty()) {
                                currentRepresentation.explicitRepresentation.setComplete();
                                return;
                            } else {
                                final var cur = remaining.cursor();
                                Preconditions.checkState(cur.moveNext());
                                newValue = cur.elem();
                            }
                        } else {
                            final IntSetView cachedKeys = currentRepresentation.explicitRepresentation.getCacheView().keySet();
                            newValue = cachedKeys.isEmpty() ? 0 : cachedKeys.statistics().highestValue() + 1;
                        }
                        literalToCache = LitExprConverter.toLitExpr(newValue, decl.getType());
                    }

                    final MutableValuation val = new MutableValuation();
                    val.put(decl, literalToCache);
                    expr = ExprUtils.simplify(expr, val);

                    if (currentRepresentation.explicitRepresentation.getCacheView().containsKey(LitExprConverter.toInt(literalToCache))) {
                        childNode = currentRepresentation.explicitRepresentation.getCacheView().get(LitExprConverter.toInt(literalToCache));
                        assert lower.isEmpty() || childNode.isOn(lower.get());
                    } else {

                        final MddExpressionTemplate template = MddExpressionTemplate.of((Expr<BoolType>) expr, o -> (VarDecl) o, currentRepresentation.solverSupplier);
                        childNode = lower.get().checkInNode(template);

                        currentRepresentation.explicitRepresentation.cacheNode(LitExprConverter.toInt(literalToCache), childNode);
                    }
                }

                Preconditions.checkArgument(childNode.getRepresentation() instanceof MddExpressionRepresentation);
                currentRepresentation = (MddExpressionRepresentation) childNode;
                variable = lower.orElse(null);
            }
        }

        private void setCurrentRepresentation(MddExpressionRepresentation representation) {
            this.currentRepresentation = currentRepresentation;
            pushNegatedAssignments();
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
             * The status of the result.
             * FAILED: no further edges are possible
             * SINGLE_EDGE: a single edge was found
             * DEFAULT_EDGE: the node is a level-skip and has a default value
             */
            public enum Status {
                FAILED, SINGLE_EDGE, DEFAULT_EDGE
            }

        }
    }
}
