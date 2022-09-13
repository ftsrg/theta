package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

/**
 * The interface of the 'traverser robots' that are responsible for enumerating a subtree represented by a symbolic mdd node
 */
public interface MddSymbolicNodeTraverser {

    /**
     * Gets the current node.
     * @return the current node
     */
    MddSymbolicNodeImpl getCurrentNode();

    /**
     * Return to the node where the last {@link #moveDown(int)}} was issued. Can't move beyond the starting node.
     * @return the new node
     */
    MddSymbolicNodeImpl moveUp();

    /**
     * Move down along an edge.
     * @param assignment the key of the edge
     * @return the new node
     */
    MddSymbolicNodeImpl moveDown(int assignment);

    /**
     * Query the next edge that wasn't cached yet. Doesn't guarantee an ordering.
     * @return the result of the query
     */
    QueryResult queryEdge();

    /**
     * Check whether an edge exists without moving down.
     * @param assignment the key of the edge to check
     * @return true if the edge exists, false otherwise
     */
    boolean queryEdge(int assignment); //return node, peakDown

    /**
     * Return the target of an edge if it exists without moving down along the edge.
     * @param assignment the key of the edge
     * @return the target of the edge if exists
     */
    MddSymbolicNodeImpl peakDown(int assignment);

    /**
     * Represents the result of querying an edge
     */
    class QueryResult{
        private final Status status;

        private final int key;

        private QueryResult(int key, Status status) {
            this.status = status;
            this.key = key;
        }

        public static QueryResult singleEdge(int key){
            return new QueryResult(key, Status.SINGLE_EDGE);
        }

        public static QueryResult failed(){
            return new QueryResult(-1, Status.FAILED);
        }

        public static QueryResult defaultEdge(){
            return new QueryResult(-1, Status.DEFAULT_EDGE);
        }

        public int getKey() {
            return key;
        }

        public Status getStatus() {
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

//    public static class ExplicitRepresentation {
//        private final HashIntObjMap<MddSymbolicNode> cache;
//        private final GrowingIntArray edgeOrdering;
//        private MddSymbolicNode defaultValue;
//        private boolean complete;
//
//        public ExplicitRepresentation() {
//            this.cache = HashIntObjMaps.newUpdatableMap();
//            this.edgeOrdering = new GrowingIntArray(100, 100);
//            this.defaultValue = null;
//            this.complete = false;
//        }
//
//        private void cacheNode(int key, MddSymbolicNode node){
//            Preconditions.checkState(!complete);
//            this.cache.put(key, node);
//            this.edgeOrdering.add(key);
//        }
//
//        private void cacheDefault(MddSymbolicNode defaultValue){
//            Preconditions.checkState(!complete);
//            this.defaultValue = defaultValue;
//        }
//
//        private void setComplete(){
//            this.complete = true;
//        }
//
//        public IntObjMapView<MddSymbolicNode> getCacheView(){
//            return IntObjMapView.of(cache, defaultValue);
//        }
//
//        public boolean isComplete(){
//            return complete;
//        }
//
//        public int getEdge(int index){
//            return edgeOrdering.get(index);
//        }
//
//        public int getSize(){
//            return edgeOrdering.getSize();
//        }

//    }
//    protected static void cacheNode(MddSymbolicNode parent, int key, MddSymbolicNode child){
//        parent.getExplicitRepresentation().cacheNode(key, child);
//    }
//
//    protected static void cacheDefault(MddSymbolicNode parent, MddSymbolicNode child){
//        parent.getExplicitRepresentation().cacheDefault(child);
//    }
//
//    protected static void setComplete(MddSymbolicNode node){
//        node.getExplicitRepresentation().setComplete();
//    }
//
}
