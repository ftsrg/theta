package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;

import java.util.OptionalInt;

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
        // Terminal 0
        return null;
    }

    @Override
    public IntObjCursor<? extends MddSymbolicNode> cursor() {
        return new IncompleteMddSymbolicNodeCursor();
//        // TODO eldönteni hogy jó-e kibontani ilyenkor teljesen
//        while (!node.isComplete()) traverser.queryEdge();
//        return node.getCacheView().cursor();
    }

    @Override
    public int size() {
        if(node.isComplete()) return node.getCacheView().size();
        return -1;
    }

    private class IncompleteMddSymbolicNodeCursor implements IntObjCursor<MddSymbolicNode>{
        private int index;
        private int key;
        private MddSymbolicNode value;

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
        public MddSymbolicNode value() {
            if(index < 0) throw new IllegalStateException("Cursor is not initialized");
            return value;
        }

        @Override
        public boolean moveNext() {
            if(index < node.getExplicitRepresentation().getSize() - 1){
                index++;
                key = node.getExplicitRepresentation().getEdge(index);
                value = node.getExplicitRepresentation().getCacheView().get(key);
                return true;
            }
            else if(!node.isComplete()) {
                final OptionalInt optionalKey = traverser.queryEdge();
                if(optionalKey.isPresent()){
                    index++;
                    key = optionalKey.getAsInt();
                    value = node.getExplicitRepresentation().getCacheView().get(key);
                    return true;
                }
            }
            return false;
        }
    }
}
