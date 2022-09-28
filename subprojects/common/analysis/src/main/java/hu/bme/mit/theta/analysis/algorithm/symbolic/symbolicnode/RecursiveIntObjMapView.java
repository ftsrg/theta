package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.IntObjMapView;

public interface RecursiveIntObjMapView<T> extends IntObjMapView<T> {

    RecursiveCursor<? extends T> cursor();

}
