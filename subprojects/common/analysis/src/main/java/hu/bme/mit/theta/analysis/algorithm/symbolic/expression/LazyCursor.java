package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import com.koloboke.collect.set.hash.HashIntSets;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.java.mdd.MddSymbolicNode;

import java.util.function.Consumer;
import java.util.function.Supplier;

public class LazyCursor<T extends MddSymbolicNode> implements IntObjCursor<T> {

    private final Supplier<Pair<Integer, MddSymbolicNode>> initializer;
    private final Consumer<Pair<Integer, MddSymbolicNode>> cacher;

    private int currentKey;
    private MddSymbolicNode currentValue;

    public LazyCursor(Supplier<Pair<Integer, MddSymbolicNode>> initializer, Consumer<Pair<Integer, MddSymbolicNode>> cacher) {
        this.initializer = initializer;
        this.cacher = cacher;
    }

    @Override
    public int key() {
        return 0;
    }

    @Override
    public T value() {
        return null;
    }

    @Override
    public boolean moveNext() {
        return false;
    }
}
