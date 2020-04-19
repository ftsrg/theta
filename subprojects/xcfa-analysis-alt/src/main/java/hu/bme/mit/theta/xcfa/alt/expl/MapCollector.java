package hu.bme.mit.theta.xcfa.alt.expl;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collector;
import java.util.stream.Collectors;

public final class MapCollector {
    public final static boolean DETERMINISTIC = true;

    public static <K,V, T> Collector<T, ?, Map<K,V>> normalCollector(Function<T,K> kk, Function<T, V> vv) {
        return Collectors.toUnmodifiableMap(kk, vv);
    }

    public static <K,V, T> Collector<T, ?, Map<K,V>> orderedCollector(Function<T,K> kk, Function<T, V> vv) {
        return Collector.of(
                LinkedHashMap::new,
                (c,t) -> c.put(kk.apply(t), vv.apply(t)),
                (c1, c2) -> { c1.putAll(c2); return c1; }
        );
    }

    public static <K,V, T> Collector<T, ?, Map<K,V>> collector(Function<T,K> kk, Function<T, V> vv) {
        if (DETERMINISTIC)
            return orderedCollector(kk, vv);
        return normalCollector(kk, vv);
    }
}
