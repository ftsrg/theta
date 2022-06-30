package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
import com.google.common.primitives.Ints;
import com.koloboke.collect.map.hash.HashIntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.common.GrowingIntArray;

import java.util.OptionalInt;

public abstract class MddSymbolicNodeTraverser {

    public abstract boolean isOn(final MddSymbolicNode node);

    public abstract MddSymbolicNode getCurrentNode();

    public abstract MddSymbolicNode moveUp();

    public abstract MddSymbolicNode moveDown(int assignment);

    public abstract OptionalInt queryEdge();

    public abstract boolean queryEdge(int assignment);

    public static class ExplicitRepresentation {
        private final HashIntObjMap<MddSymbolicNode> cache;
        private final GrowingIntArray edgeOrdering;
        private MddSymbolicNode defaultValue;
        private boolean complete;

        public ExplicitRepresentation() {
            this.cache = HashIntObjMaps.newUpdatableMap();
            this.edgeOrdering = new GrowingIntArray(100, 100);
            this.defaultValue = null;
            this.complete = false;
        }

        private void cacheNode(int key, MddSymbolicNode node){
            Preconditions.checkState(!complete);
            this.cache.put(key, node);
            this.edgeOrdering.add(key);
        }

        private void cacheDefault(MddSymbolicNode defaultValue){
            Preconditions.checkState(!complete);
            this.defaultValue = defaultValue;
        }

        private void setComplete(){
            this.complete = true;
        }

        public IntObjMapView<MddSymbolicNode> getCacheView(){
            return IntObjMapView.of(cache, defaultValue);
        }

        public boolean isComplete(){
            return complete;
        }

        public int getEdge(int index){
            return edgeOrdering.get(index);
        }

        public int getSize(){
            return edgeOrdering.getSize();
        }
    }

    protected static void cacheNode(MddSymbolicNode parent, int key, MddSymbolicNode child){
        parent.getExplicitRepresentation().cacheNode(key, child);
    }

    protected static void cacheDefault(MddSymbolicNode parent, MddSymbolicNode child){
        parent.getExplicitRepresentation().cacheDefault(child);
    }

    protected static void setComplete(MddSymbolicNode node){
        node.getExplicitRepresentation().setComplete();
    }
}
