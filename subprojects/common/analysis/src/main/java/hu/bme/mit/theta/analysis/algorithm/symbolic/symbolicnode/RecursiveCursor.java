package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.IntObjCursor;

public interface RecursiveCursor<T> extends IntObjCursor<T>, AutoCloseable {

    boolean moveTo(int key);

    RecursiveCursor valueCursor();

    @Override
    void close();

}
