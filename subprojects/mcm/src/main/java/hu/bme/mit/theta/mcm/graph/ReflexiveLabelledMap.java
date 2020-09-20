package hu.bme.mit.theta.mcm.graph;

import hu.bme.mit.theta.common.Tuple2;

import java.util.*;

public class ReflexiveLabelledMap<K, V, L>{

    private final Map<K, Set<Tuple2<L, V>>> forwardMap;
    private final Map<V, Set<Tuple2<L, K>>> reverseMap;

    public ReflexiveLabelledMap() {
        forwardMap = new HashMap<>();
        reverseMap = new HashMap<>();
    }

    public Set<K> getKeySet() {
        return forwardMap.keySet();
    }

    public Set<V> getValueSet() {
        return reverseMap.keySet();
    }

    public Set<Tuple2<L, K>> getKeys(V v) {
        return Collections.unmodifiableSet(reverseMap.get(v));
    }

    public Set<Tuple2<L, V>> getValues(K k) {
        return Collections.unmodifiableSet(forwardMap.getOrDefault(k, new HashSet<>()));
    }

    public void addPair(K k, V v, L l) {
        forwardMap.putIfAbsent(k, new HashSet<>());
        forwardMap.get(k).add(Tuple2.of(l, v));
        reverseMap.putIfAbsent(v, new HashSet<>());
        reverseMap.get(v).add(Tuple2.of(l, k));
    }

    public Tuple2<Optional<K>, Optional<V>> removePair(K k, V v, L l) {
        K rmK = null;
        V rmV = null;
        forwardMap.get(k).remove(Tuple2.of(v, l));
        if(forwardMap.get(k).isEmpty()){
            forwardMap.remove(k);
            rmK = k;
        }
        reverseMap.get(v).remove(Tuple2.of(k, l));
        if(reverseMap.get(v).isEmpty()) {
            reverseMap.remove(v);
            rmV = v;
        }
        return Tuple2.of(Optional.ofNullable(rmK), Optional.ofNullable(rmV));
    }

    public ReflexiveLabelledMap<K, V, L> duplicate() {
        ReflexiveLabelledMap<K, V, L> ret = new ReflexiveLabelledMap<>();
        forwardMap.forEach((k, vs) -> ret.forwardMap.put(k, new HashSet<>(vs)));
        reverseMap.forEach((k, vs) -> ret.reverseMap.put(k, new HashSet<>(vs)));
        return ret;
    }

}
