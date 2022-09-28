package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;

import java.io.IOException;

public class MddSymbolicNodeRecursiveCursor implements RecursiveCursor<MddSymbolicNode> {

    private final MddSymbolicNodeRecursiveCursor parent;
    private final MddSymbolicNodeTraverser traverser;
    private boolean blocked = false;
    private boolean closed = false;

    private int index;
    private int key;
    private MddSymbolicNode value;

    public MddSymbolicNodeRecursiveCursor(final MddSymbolicNodeRecursiveCursor parent,
                                          final MddSymbolicNodeTraverser traverser) {
        this.parent = parent;
        this.traverser = traverser;
        this.index = -1;
        this.key = -1;
        this.value = null;
    }

    @Override
    public boolean moveTo(int key) {
        Preconditions.checkState(!blocked, "Cursor can't be moved until its children are disposed of");
        Preconditions.checkState(!closed, "Cursor can't be moved if it was closed");

        var node = traverser.getCurrentNode();
        if(node.getExplicitRepresentation().getCacheView().containsKey(key) || !node.isComplete() && traverser.queryEdge(key)){
            this.key = key;
            this.value = node.getExplicitRepresentation().getCacheView().get(key);
            return true;
        }
        return false;

    }

    @Override
    public RecursiveCursor<MddSymbolicNode> valueCursor() {
        this.blocked = true;
        this.traverser.moveDown(key);
        return new MddSymbolicNodeRecursiveCursor(this, traverser);
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
        Preconditions.checkState(!blocked, "Cursor can't be moved until its children are disposed of");
        Preconditions.checkState(!closed, "Cursor can't be moved if it was closed");

        var node = traverser.getCurrentNode();
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

    @Override
    public void close() {
        this.closed = true;
        if(parent != null) {
            traverser.moveUp();
            parent.unblock();
        }
    }

    private void unblock(){
        this.blocked = false;
    }

}
