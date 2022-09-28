package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.IntObjMapView;

public class DefaultRecursiveIntObjMapViewImpl<T> implements RecursiveIntObjMapView<T>{

    private final IntObjMapView<T> forwardingTarget;

    public DefaultRecursiveIntObjMapViewImpl(IntObjMapView<T> forwardingTarget) {
        this.forwardingTarget = forwardingTarget;
    }

    @Override
    public boolean isEmpty() {
        return forwardingTarget.isEmpty();
    }

    @Override
    public boolean isProcedural() {
        return forwardingTarget.isProcedural();
    }

    @Override
    public boolean containsKey(int i) {
        return forwardingTarget.containsKey(i);
    }

    @Override
    public T get(int i) {
        return forwardingTarget.get(i);
    }

    @Override
    public T defaultValue() {
        return forwardingTarget.defaultValue();
    }

    @Override
    public RecursiveCursor<? extends T> cursor() {
        return new DefaultRecursiveCursorImpl<>(forwardingTarget.cursor());
    }

    @Override
    public int size() {
        return forwardingTarget.size();
    }
}
