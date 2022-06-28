package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;

public class IncompleteMddSymbolicNodeInterpretation implements IntObjMapView<MddSymbolicNode> {

    private final MddSymbolicNode node;
    private final MddSymbolicNodeTraverser traverser;

    public IncompleteMddSymbolicNodeInterpretation(MddSymbolicNode node, MddSymbolicNodeTraverser traverser) {
        this.node = node;
        this.traverser = traverser;
    }

    @Override
    public boolean isEmpty() {
        // TODO ha default value van akkor mi?
        if(!node.getCacheView().isEmpty()) return false;
        traverser.queryNext();
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
        return traverser.queryNext(key);
    }

    @Override
    public MddSymbolicNode get(int key) {
        traverser.queryNext(key);
        // Traverser is responsible for caching
        return node.getCacheView().get(key);
    }

    @Override
    public MddSymbolicNode defaultValue() {
        // Terminal 0
        return null;
    }

    @Override
    public IntObjCursor<? extends MddSymbolicNode> cursor() {
        // TODO eldönteni hogy jó-e kibontani ilyenkor teljesen
        while (!node.isComplete()) traverser.queryNext();
        return node.getCacheView().cursor();
    }

    @Override
    public int size() {
        if(node.isComplete()) return node.getCacheView().size();
        return -1;
    }

    // TODO ez csak akkor működik, ha a koloboke intobjmapview cursor-a tudja kezelni ha az alatta lévő mapbe elemet raknak
    // sajnos nem
//    private class IncompleteExpressionNodeCursor implements IntObjCursor<ExpressionNode>{
//        private final IntObjCursor<? extends ExpressionNode> cacheCursor = node.getCacheView().cursor();
//
//        @Override
//        public int key() {
//            return cacheCursor.key();
//        }
//
//        @Override
//        public ExpressionNode value() {
//            return cacheCursor.value();
//        }
//
//        @Override
//        public boolean moveNext() {
//            if(cacheCursor.moveNext()) return true;
//            else if(!node.isComplete()) traverser.queryAssignment();
//            return cacheCursor.moveNext();
//        }
//    }
}
