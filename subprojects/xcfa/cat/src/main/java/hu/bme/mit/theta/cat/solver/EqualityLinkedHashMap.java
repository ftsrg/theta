package hu.bme.mit.theta.cat.solver;

import hu.bme.mit.theta.common.Tuple2;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class EqualityLinkedHashMap<K, V> implements Map<K, V> {
	private final Map<K, Collection<Tuple2<K, Integer>>> buckets;
	private final List<V> heap;

	public EqualityLinkedHashMap() {
		buckets = new LinkedHashMap<>();
		heap = new LinkedList<>();
	}

	public EqualityLinkedHashMap(final EqualityLinkedHashMap<K, V> map) {
		buckets = new LinkedHashMap<>(map.buckets);
		heap = new LinkedList<>(map.heap);
	}

	@Override
	public int size() {
		return heap.size();
	}

	@Override
	public boolean isEmpty() {
		return heap.isEmpty();
	}

	@Override
	public boolean containsKey(Object o) {
		final Collection<Tuple2<K, Integer>> entries = buckets.get(o);
		if (entries != null) {
			for (Tuple2<K, Integer> entry : entries) {
				if (entry.get1() == o) return true;
			}
		}
		return false;
	}

	@Override
	public boolean containsValue(Object o) {
		return heap.contains(o);
	}

	private Integer getIndex(Object o) {
		final Collection<Tuple2<K, Integer>> entries = buckets.get(o);
		if (entries != null) {
			for (Tuple2<K, Integer> entry : entries) {
				if (entry.get1() == o) return entry.get2();
			}
		}
		return null;
	}

	@Override
	public V get(Object o) {
		final Integer index = getIndex(o);
		return index == null ? null : heap.get(index);
	}

	@Override
	public V put(K k, V v) {
		final Integer index = getIndex(k);
		if (index == null) {
			buckets.putIfAbsent(k, new ArrayList<>());
			buckets.get(k).add(Tuple2.of(k, heap.size()));
			heap.add(v);
		} else {
			heap.remove((int) index);
			heap.add(index, v);
		}
		return v;
	}

	@Override
	public V remove(Object o) {
		final Integer index = getIndex(o);
		if (index == null) {
			return null;
		} else {
			final V v = heap.get(index);
			buckets.get(o).remove(Tuple2.of(o, index));
			heap.remove((int) index);
			return v;
		}
	}

	@Override
	public void putAll(Map<? extends K, ? extends V> map) {
		map.forEach(this::put);

	}

	@Override
	public void clear() {
		heap.clear();
		buckets.clear();
	}

	@Override
	public Set<K> keySet() {
		throw new UnsupportedOperationException("Key set is not possible for an EqualityLinkedHashMap!");
	}

	@Override
	public Collection<V> values() {
		return heap;
	}

	@Override
	public Set<Entry<K, V>> entrySet() {
		Set<Entry<K, V>> ret = new LinkedHashSet<>();
		for (Entry<K, Collection<Tuple2<K, Integer>>> entry : buckets.entrySet()) {
			K k = entry.getKey();
			Collection<Tuple2<K, Integer>> tuple2s = entry.getValue();
			for (Tuple2<K, Integer> tuple2 : tuple2s) {
				ret.add(Map.entry(k, heap.get(tuple2.get2())));
			}
		}
		return ret;
	}
}
