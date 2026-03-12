/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.common.collection.factory;

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.ObjectOpenHashSet;
import java.util.Collection;
import java.util.Map;
import java.util.Set;

public class FastUtilCollectionFactory implements CollectionFactory {

    @Override
    public <K, V> Map<K, V> createMap() {
        return new Object2ObjectOpenHashMap<>();
    }

    @Override
    public <K, V> Map<K, V> createMap(int initialCapacity) {
        return new Object2ObjectOpenHashMap<>(initialCapacity);
    }

    @Override
    public <K, V> Map<K, V> createMap(int initialCapacity, float loadFactor) {
        return new Object2ObjectOpenHashMap<>(initialCapacity, loadFactor);
    }

    @Override
    public <K, V> Map<K, V> createMap(Map<? extends K, ? extends V> m) {
        return new Object2ObjectOpenHashMap<>(m);
    }

    @Override
    public <E> Set<E> createSet() {
        return new ObjectOpenHashSet<>();
    }

    @Override
    public <E> Set<E> createSet(int initialCapacity) {
        return new ObjectOpenHashSet<>(initialCapacity);
    }

    @Override
    public <E> Set<E> createSet(int initialCapacity, float loadFactor) {
        return new ObjectOpenHashSet<>(initialCapacity, loadFactor);
    }

    @Override
    public <E> Set<E> createSet(Collection<? extends E> c) {
        return new ObjectOpenHashSet<>(c);
    }
}
