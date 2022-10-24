package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.RecursiveIntObjMapView;

/**
 * Provides an interpretation for symbolic nodes.
 * Wraps a node and a traverser and makes the traverser enumerate only what is necessary.
 */
public class MddSymbolicNodeInterpretation implements RecursiveIntObjMapView<MddSymbolicNode> {

    private final MddSymbolicNode node;
    private final MddSymbolicNodeTraverser traverser;

    public MddSymbolicNodeInterpretation(MddSymbolicNode node, MddSymbolicNodeTraverser traverser) {
        this.node = node;
        this.traverser = traverser;
    }

    public MddSymbolicNode getNode() {
        return node;
    }

    @Override
    public boolean isEmpty() {
        // TODO ha default value van akkor mi?
        if(!node.getCacheView().isEmpty()) return false;
        traverser.queryEdge();
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
        return traverser.queryEdge(key);
    }

    @Override
    public MddSymbolicNode get(int key) {
        traverser.queryEdge(key);
        // Traverser is responsible for caching
        return node.getCacheView().get(key);
    }

    @Override
    public MddSymbolicNode defaultValue() {
        return node.getCacheView().defaultValue();
    }

    @Override
    public RecursiveCursor<? extends MddSymbolicNode> cursor() {
        return new MddSymbolicNodeRecursiveCursor(null, traverser); // TODO new traverser
    }

    @Override
    public int size() {
        if(node.isComplete()) return node.getCacheView().size();
        return -1;
    }

//    /**
//     * A cursor implementation for incomplete symbolic nodes.
//     */
//    private class IncompleteMddSymbolicNodeCursor implements IntObjCursor<MddSymbolicNode>{
//        private int index;
//        private int key;
//        private MddSymbolicNode value;
//
//        private IncompleteMddSymbolicNodeCursor(){
//            this.index = -1;
//            this.key = -1;
//            this.value = null;
//        }
//
//        @Override
//        public int key() {
//            if(index < 0) throw new IllegalStateException("Cursor is not initialized");
//            return key;
//        }
//
//        @Override
//        public MddSymbolicNode value() {
//            if(index < 0) throw new IllegalStateException("Cursor is not initialized");
//            return value;
//        }
//
//        /**
//         * Uses values from the cache as long as possible. Uses the traverser to query edges when all edges from the cache were used.
//         * @return true if the move was successful
//         */
//        @Override
//        public boolean moveNext() {
//            if(index < node.getExplicitRepresentation().getSize() - 1){
//                index++;
//                key = node.getExplicitRepresentation().getEdge(index);
//                value = node.getExplicitRepresentation().getCacheView().get(key);
//                return true;
//            }
//            else if(!node.isComplete()) {
//                final MddSymbolicNodeTraverser.QueryResult queryResult = traverser.queryEdge();
//                if(queryResult.getStatus() == MddSymbolicNodeTraverser.QueryResult.Status.SINGLE_EDGE){
//                    index++;
//                    key = queryResult.getKey();
//                    value = node.getExplicitRepresentation().getCacheView().get(key);
//                    return true;
//                }
//            }
//            return false;
//        }
//    }
}
