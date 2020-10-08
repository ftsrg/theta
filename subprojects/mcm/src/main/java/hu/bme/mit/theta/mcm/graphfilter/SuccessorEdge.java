package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.*;


public class SuccessorEdge extends Filter {
    private final Filter source;
    private final Filter target;
    private final Set<String> edgeLabel;
    private Set<GraphOrNodeSet> last;
    private final Map<MemoryAccess, Set<MemoryAccess>> edges;
    private final Map<MemoryAccess, Set<MemoryAccess>> reverse;
    private final Map<MemoryAccess, Set<MemoryAccess>> reachable;
    private final Map<MemoryAccess, Set<MemoryAccess>> reachableFrom;
    private boolean changed;

    public SuccessorEdge(Filter source, Filter target, Set<String> edgeLabel) {
        this.source = source;
        this.target = target;
        this.edgeLabel = edgeLabel;
        this.last = new HashSet<>();
        edges = new HashMap<>();
        reverse = new HashMap<>();
        reachable = new HashMap<>();
        reachableFrom = new HashMap<>();
        this.changed = false;
    }

    public SuccessorEdge(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads, Filter source, Filter target, Set<String> edgeLabel, Set<GraphOrNodeSet> last, Map<MemoryAccess, Set<MemoryAccess>> edges, Map<MemoryAccess, Set<MemoryAccess>> reverse, Map<MemoryAccess, Set<MemoryAccess>> reachable, Map<MemoryAccess, Set<MemoryAccess>> reachableFrom, boolean changed) {
        this.source = source.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.target = target.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.edgeLabel = edgeLabel;
        this.edges = new HashMap<>();
        edges.forEach((memoryAccess, memoryAccesses) -> this.edges.put(memoryAccess, new HashSet<>(memoryAccesses)));
        this.reverse = new HashMap<>();
        reverse.forEach((memoryAccess, memoryAccesses) -> this.reverse.put(memoryAccess, new HashSet<>(memoryAccesses)));
        this.reachable = new HashMap<>();
        reachable.forEach((memoryAccess, memoryAccesses) -> this.reachable.put(memoryAccess, new HashSet<>(memoryAccesses)));
        this.reachableFrom = new HashMap<>();
        reachableFrom.forEach((memoryAccess, memoryAccesses) -> this.reachableFrom.put(memoryAccess, new HashSet<>(memoryAccesses)));
        this.last = new HashSet<>();
        last.forEach(graphOrNodeSet -> this.last.add(graphOrNodeSet.duplicate()));
        this.changed = changed;
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        if(edgeLabel.contains(label)) {
            if(!edges.containsKey(source) || !edges.containsKey(target) || !edges.get(source).contains(target)) {
                changed = true;
            }
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
            reachable.get(source).add(target);
            reachableFrom.get(target).add(source);
        }
        Set<GraphOrNodeSet> src = this.source.filterMk(source, target, label, isFinal);
        Set<GraphOrNodeSet> dst = this.target.filterMk(source, target, label, isFinal);
        return getSuccessors(src, dst, label);

    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        if(edgeLabel.contains(label)) {
            if(edges.get(source).contains(target)) {
                changed = true;
            }
            Set<MemoryAccess> potRemove = new HashSet<>();
            potRemove.add(target);
            potRemove.addAll(reachable.get(target));
            Set<MemoryAccess> remove = new HashSet<>(potRemove);
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
        }

        Set<GraphOrNodeSet> src = this.source.filterRm(source, target, label);
        Set<GraphOrNodeSet> dst = this.target.filterRm(source, target, label);

        return getSuccessors(src, dst, label);

    }

    @Override
    public Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new SuccessorEdge(forEachNodes, forEachVars, forEachThreads, source, target, edgeLabel, last, edges, reverse, reachable, reachableFrom, changed);
    }

    private Set<GraphOrNodeSet> getSuccessors(Set<GraphOrNodeSet> srcSet, Set<GraphOrNodeSet> dstSet, String label) {
        boolean changed = false;
        for (GraphOrNodeSet src : srcSet) {
            if(src.isChanged()) {
                changed = true;
                src.setChanged(false);
            }
        }
        for (GraphOrNodeSet dst : dstSet) {
            if(dst.isChanged()) {
                changed = true;
                dst.setChanged(false);
            }
        }
        if(!changed && !this.changed) {
            return last;
        }
        this.changed = false;
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (GraphOrNodeSet src : srcSet) {
            for (GraphOrNodeSet dst : dstSet) {
                if(src.isGraph() || dst.isGraph()) {
                    throw new UnsupportedOperationException("Cannot have a graph as a source and/or target!");
                }
                else {
                    Graph graph = Graph.empty();
                    for (MemoryAccess s : src.getNodeSet()) {
                        for (MemoryAccess t : reachable.getOrDefault(s, new HashSet<>())) {
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
