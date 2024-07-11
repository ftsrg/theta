/*
 *  Copyright 2024 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm.mdd.model.impl;

import com.koloboke.collect.set.IntSet;
import com.koloboke.collect.set.hash.HashIntSets;

import hu.bme.mit.delta.collections.IntCursor;
import hu.bme.mit.theta.analysis.algorithm.mdd.model.DomainRegistry;

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
