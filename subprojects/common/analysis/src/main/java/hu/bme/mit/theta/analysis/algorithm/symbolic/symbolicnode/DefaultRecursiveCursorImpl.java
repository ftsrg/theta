package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.IntObjCursor;

public class DefaultRecursiveCursorImpl<T> implements RecursiveCursor<T>{

    private final IntObjCursor<T> forwardingTarget;

    public DefaultRecursiveCursorImpl(IntObjCursor<T> forwardingTarget){
        this.forwardingTarget = forwardingTarget;
    }

    @Override
    public boolean moveTo(int key) {
        return false;
    }

    @Override
    public RecursiveCursor<T> valueCursor() {
        //return new DefaultRecursiveCursorImpl<>(forwardingTarget.value().cursor(), this);
        return null;
    }

    @Override
    public int key() {
        return forwardingTarget.key();
    }

    @Override
    public T value() {
        return forwardingTarget.value();
    }

    @Override
    public boolean moveNext() {
        return forwardingTarget.moveNext();
    }

    @Override
    public void close() {}
}
