package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
public interface MddSymbolicNodeTraverser {

    MddSymbolicNode getCurrentNode();

    MddSymbolicNode moveUp();

    MddSymbolicNode moveDown(int assignment);

    QueryResult queryEdge();

    boolean queryEdge(int assignment); //return node, peakDown

    MddSymbolicNode peakDown(int assignment);

    class QueryResult{
        private final Status status;

        private final int key;
        public QueryResult(int key) {
            this.status = Status.SINGLE_EDGE;
            this.key = key;
        }

        public QueryResult(Status status) {
            Preconditions.checkArgument(status != Status.SINGLE_EDGE);
            this.status = status;
            this.key = -1;
        }

        public int getKey() {
            return key;
        }

        public Status getStatus() {
            return status;
        }
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
