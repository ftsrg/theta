package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


public class SuccessorEdge<T extends MemoryAccess> extends Filter<T> {
    private final Filter<T> source;
    private final Filter<T> target;
    private final String edgeLabel;
    private Set<GraphOrNodeSet<T>> last;
    private final Map<T, Set<T>> edges;
    private final Map<T, Set<T>> reverse;
    private final Map<T, Set<T>> reachable;
    private final Map<T, Set<T>> reachableFrom;

    public SuccessorEdge(Filter<T> source, Filter<T> target, String edgeLabel) {
        this.source = source;
        this.target = target;
        this.edgeLabel = edgeLabel;
        this.last = new HashSet<>();
        edges = new HashMap<>();
        reverse = new HashMap<>();
        reachable = new HashMap<>();
        reachableFrom = new HashMap<>();
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        if(!label.equals(edgeLabel)) {
            return last;
        }
        else {
            edges.putIfAbsent(source, new HashSet<>());
            reverse.putIfAbsent(target, new HashSet<>());
            reachable.putIfAbsent(source, new HashSet<>());
            reachableFrom.putIfAbsent(source, new HashSet<>());
            reachableFrom.putIfAbsent(target, new HashSet<>());

            edges.get(source).add(target);
            reverse.get(target).add(source);
            reachableFrom.get(target).add(source);
            reachableFrom.get(source).forEach(t -> {
                reachableFrom.get(target).add(t);
                reachable.get(t).add(target);
            });
            Set<GraphOrNodeSet<T>> src = this.source.filterMk(source, target, label, isFinal);
            Set<GraphOrNodeSet<T>> dst = this.target.filterMk(source, target, label, isFinal);
            return getSuccessors(src, dst, label);

        }
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label) {
        if(!label.equals(edgeLabel)) {
            return last;
        }
        else if (edges.get(source) == null || !edges.get(source).contains(target)) {
            throw new UnsupportedOperationException("Trying to remove a non-existant edge.");
        }
        else {
            Set<T> potRemove = new HashSet<>();
            potRemove.add(target);
            potRemove.addAll(reachable.get(target));
            Set<T> remove = new HashSet<>(potRemove);
            potRemove.forEach(t -> reverse.get(t).forEach(t1 -> {
                if (!potRemove.contains(t1)) {
                    remove.remove(t);
                    remove.removeAll(reachable.get(t));
                }
            }));

            reachableFrom.forEach((t1, ts) -> ts.removeAll(remove));
            reachable.forEach((t, ts) -> ts.removeAll(remove));
            remove.forEach(t -> {
                reachable.remove(t);
                reachableFrom.remove(t);
            });

            edges.get(source).remove(target);
            reverse.get(target).remove(source);

            Set<GraphOrNodeSet<T>> src = this.source.filterRm(source, target, label);
            Set<GraphOrNodeSet<T>> dst = this.target.filterRm(source, target, label);

            return getSuccessors(src, dst, label);

        }
    }

    private Set<GraphOrNodeSet<T>> getSuccessors(Set<GraphOrNodeSet<T>> srcSet, Set<GraphOrNodeSet<T>> dstSet, String label) {
        boolean changed = false;
        for (GraphOrNodeSet<T> src : srcSet) {
            if(src.isChanged()) {
                changed = true;
                src.setChanged(false);
            }
        }
        for (GraphOrNodeSet<T> dst : dstSet) {
            if(dst.isChanged()) {
                changed = true;
                dst.setChanged(false);
            }
        }
        if(!changed) {
            return last;
        }
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (GraphOrNodeSet<T> src : srcSet) {
            for (GraphOrNodeSet<T> dst : dstSet) {
                if(src.isGraph() || dst.isGraph()) {
                    throw new UnsupportedOperationException("Cannot have a graph as a source and/or target!");
                }
                else {
                    Graph<T> graph = Graph.create(false);
                    for (T s : src.getNodeSet()) {
                        for (T t : reachable.get(s)) {
                            if(dst.getNodeSet().contains(t)) {
                                graph.addEdge(s, t, false);
                            }
                        }
                    }

                    retSet.add(GraphOrNodeSet.of(graph));
                }
            }
        }
        return last = retSet;
    }
}
