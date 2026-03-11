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
package hu.bme.mit.theta.common.collection;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.collection.factory.CollectionFactory;
import hu.bme.mit.theta.common.collection.factory.FastUtilCollectionFactory;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

public class CollectionUtil {

    private static CollectionFactory collectionFactory = new FastUtilCollectionFactory();

    public static void setCollectionFactory(final CollectionFactory collectionFactory) {
        checkNotNull(collectionFactory);
        CollectionUtil.collectionFactory = collectionFactory;
    }

    public static <K, V> Map<K, V> createMap() {
        return collectionFactory.createMap();
    }

    public static <K, V> Map<K, V> createMap(int initialCapacity) {
        return collectionFactory.createMap(initialCapacity);
    }

    public static <K, V> Map<K, V> createMap(int initialCapacity, float loadFactor) {
        return collectionFactory.createMap(initialCapacity, loadFactor);
    }

    public static <K, V> Map<K, V> createMap(Map<? extends K, ? extends V> m) {
        return collectionFactory.createMap(m);
    }

    public static <E> Set<E> createSet() {
        return collectionFactory.createSet();
    }

    public static <E> Set<E> createSet(int initialCapacity) {
        return collectionFactory.createSet(initialCapacity);
    }

    public static <E> Set<E> createSet(int initialCapacity, float loadFactor) {
        return collectionFactory.createSet(initialCapacity, loadFactor);
    }

    public static <E> Set<E> createSet(Collection<? extends E> c) {
        return collectionFactory.createSet(c);
    }
}
