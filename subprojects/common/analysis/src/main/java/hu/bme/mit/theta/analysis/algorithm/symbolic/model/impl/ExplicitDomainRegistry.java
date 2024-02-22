package hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl;

import com.koloboke.collect.set.IntSet;
import com.koloboke.collect.set.hash.HashIntSets;

import hu.bme.mit.delta.collections.IntCursor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.DomainRegistry;

// TODO: this cannot describe infinite domains
public final class ExplicitDomainRegistry implements DomainRegistry {
    private final IntSet values = HashIntSets.newMutableSet();

    @Override
    public void confirm(int value) {
        values.add(value);
    }

    @Override
    public void clear() {
        values.clear();
    }

    @Override
    public boolean contains(final int v) {
        return values.contains(v);
    }

    @Override
    public IntCursor cursor() {
        return IntCursor.of(values.cursor());
    }

    @Override
    public boolean isEmpty() {
        return values.isEmpty();
    }

    @Override
    public boolean isProcedural() {
        return false;
    }

    @Override
    public int size() {
        return values.size();
    }
}
