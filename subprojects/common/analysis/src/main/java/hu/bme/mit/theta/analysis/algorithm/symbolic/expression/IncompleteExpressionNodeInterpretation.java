package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import com.google.common.base.Preconditions;
import com.google.common.base.Supplier;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.solver.Solver;

public class IncompleteExpressionNodeInterpretation implements IntObjMapView<ExpressionNode> {

    private final ExpressionNode node;
    private final ExpressionNodeTraverser traverser;

    public IncompleteExpressionNodeInterpretation(ExpressionNode node, Supplier<Solver> solverSupplier) {
        this.node = node;
        this.traverser = new ExpressionNodeTraverser(node, solverSupplier);
    }

    @Override
    public boolean isEmpty() {
        // TODO ha default value van akkor mi?
        if(!node.getCacheView().isEmpty()) return false;
        traverser.queryAssignment();
        return node.getCacheView().isEmpty();
    }

    @Override
    public boolean isProcedural() {
        return true;
    }

    @Override
    public boolean containsKey(int key) {
        // Check if sat -> true
        // Cache model if found
        return traverser.queryAssignment(LitExprConverter.toLitExpr(key, node.getDecision().second.getTraceInfo(Decl.class).getType()));
    }

    @Override
    public ExpressionNode get(int key) {
        traverser.queryAssignment(LitExprConverter.toLitExpr(key, node.getDecision().second.getTraceInfo(Decl.class).getType()));
        // Simplify expr, ask for new node with simplified expr, cache child
        // Traverser is responsible for caching
        return node.getCacheView().get(key);
    }

    @Override
    public ExpressionNode defaultValue() {
        // Terminal 0
        return null;
    }

    @Override
    public IntObjCursor<? extends ExpressionNode> cursor() {
        return new IncompleteExpressionNodeCursor();
    }

    @Override
    public int size() {
        if(node.isComplete()) return node.getCacheView().size();
        return -1;
    }

    // TODO ez csak akkor működik, ha a koloboke intobjmapview cursor-a tudja kezelni ha az alatta lévő mapbe elemet raknak
    private class IncompleteExpressionNodeCursor implements IntObjCursor<ExpressionNode>{
        private final IntObjCursor<? extends ExpressionNode> cacheCursor = node.getCacheView().cursor();

        @Override
        public int key() {
            return cacheCursor.key();
        }

        @Override
        public ExpressionNode value() {
            return cacheCursor.value();
        }

        @Override
        public boolean moveNext() {
            if(cacheCursor.moveNext()) return true;
            else if(!node.isComplete()) traverser.queryAssignment();
            return cacheCursor.moveNext();
        }
    }
}
