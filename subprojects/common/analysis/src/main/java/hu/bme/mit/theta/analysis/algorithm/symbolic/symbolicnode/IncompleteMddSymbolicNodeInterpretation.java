package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.java.mdd.MddNode;

/**
 * Provides an interpretation for nodes that haven't been fully enumerated yet.
 * Wraps a node and a traverser and makes the traverser enumerate only what is necessary.
 */
public class IncompleteMddSymbolicNodeInterpretation implements IntObjMapView<MddNode> {

    private final MddSymbolicNodeImpl node;
    private final MddSymbolicNodeTraverser traverser;

    public IncompleteMddSymbolicNodeInterpretation(MddSymbolicNodeImpl node, MddSymbolicNodeTraverser traverser) {
        this.node = node;
        this.traverser = traverser;
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
    public MddNode get(int key) {
        traverser.queryEdge(key);
        // Traverser is responsible for caching
        return node.getCacheView().get(key);
    }

    @Override
    public MddNode defaultValue() {
        return node.getCacheView().defaultValue();
    }

    @Override
    public IntObjCursor<? extends MddNode> cursor() {
        if(node.isComplete()) return node.getCacheView().cursor();
        return new IncompleteMddSymbolicNodeCursor();
    }

    @Override
    public int size() {
        if(node.isComplete()) return node.getCacheView().size();
        return -1;
    }

    /**
     * A cursor implementation for incomplete symbolic nodes.
     */
    private class IncompleteMddSymbolicNodeCursor implements IntObjCursor<MddNode>{
        private int index;
        private int key;
        private MddNode value;

        private IncompleteMddSymbolicNodeCursor(){
            this.index = -1;
            this.key = -1;
            this.value = null;
        }

        @Override
        public int key() {
            if(index < 0) throw new IllegalStateException("Cursor is not initialized");
            return key;
        }

        @Override
        public MddNode value() {
            if(index < 0) throw new IllegalStateException("Cursor is not initialized");
            return value;
        }

        /**
         * Uses values from the cache as long as possible. Uses the traverser to query edges when all edges from the cache were used.
         * @return true if the move was successful
         */
        @Override
        public boolean moveNext() {
            if(index < node.getExplicitRepresentation().getSize() - 1){
                index++;
                key = node.getExplicitRepresentation().getEdge(index);
                value = node.getExplicitRepresentation().getCacheView().get(key);
                return true;
            }
            else if(!node.isComplete()) {
                final MddSymbolicNodeTraverser.QueryResult queryResult = traverser.queryEdge();
                if(queryResult.getStatus() == MddSymbolicNodeTraverser.QueryResult.Status.SINGLE_EDGE){
                    index++;
                    key = queryResult.getKey();
                    value = node.getExplicitRepresentation().getCacheView().get(key);
                    return true;
                }
            }
            return false;
        }
    }
}
