/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.common.container;

import hu.bme.mit.theta.common.container.factory.ContainerFactory;
import hu.bme.mit.theta.common.container.factory.LinkedHashContainerFactory;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;

public class Containers {

    private static ContainerFactory containerFactory = new LinkedHashContainerFactory();

    public static void setContainerFactory(final ContainerFactory containerFactory) {
        checkNotNull(containerFactory);
        Containers.containerFactory = containerFactory;
    }

    public static <K, V> Map<K, V> createMap() {
        return containerFactory.createMap();
    }

    public static <K, V> Map<K, V> createMap(int initialCapacity) {
        return containerFactory.createMap(initialCapacity);
    }

    public static <K, V> Map<K, V> createMap(int initialCapacity, float loadFactor) {
        return containerFactory.createMap(initialCapacity, loadFactor);
    }

    public static <K, V> Map<K, V> createMap(Map<? extends K, ? extends V> m) {
        return containerFactory.createMap(m);
    }

    public static <E> Set<E> createSet() {
        return containerFactory.createSet();
    }

    public static <E> Set<E> createSet(int initialCapacity) {
        return containerFactory.createSet(initialCapacity);
    }

    public static <E> Set<E> createSet(int initialCapacity, float loadFactor) {
        return containerFactory.createSet(initialCapacity, loadFactor);
    }

    public static <E> Set<E> createSet(Collection<? extends E> c) {
        return containerFactory.createSet(c);
    }

}
