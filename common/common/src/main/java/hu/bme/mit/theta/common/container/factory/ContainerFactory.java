package hu.bme.mit.theta.common.container.factory;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

public interface ContainerFactory {

    <K, V> Map<K, V> createMap();

    <K, V> Map<K, V> createMap(int initialCapacity);

    <K, V> Map<K, V> createMap(int initialCapacity, float loadFactor);

    <K, V> Map<K, V> createMap(Map<? extends K,? extends V> m);

    <E> Set<E> createSet();

    <E> Set<E> createSet(int initialCapacity);

    <E> Set<E> createSet(int initialCapacity, float loadFactor);

    <E> Set<E> createSet(Collection<? extends E> c);

}
