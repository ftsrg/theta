package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.*;

public class NextEdge extends Filter {
    private final Filter source;
    private final Filter target;
    private final Set<String> edgeLabel;
    private Set<GraphOrNodeSet> last;
    private final Map<MemoryAccess, Set<MemoryAccess>> edges;
    private final Map<MemoryAccess, Set<MemoryAccess>> reverse;


    public NextEdge(Filter source, Filter target, Set<String> edgeLabel) {
        this.source = source;
        this.target = target;
        this.edgeLabel = edgeLabel;
        this.last = new HashSet<>();
        edges = new HashMap<>();
        reverse = new HashMap<>();
    }

    public NextEdge(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads, Filter source, Filter target, Set<String> edgeLabel, Set<GraphOrNodeSet> last, Map<MemoryAccess, Set<MemoryAccess>> edges, Map<MemoryAccess, Set<MemoryAccess>> reverse) {
        this.source = source.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.target = target.duplicate(forEachNodes, forEachVars, forEachThreads);
        this.edgeLabel = edgeLabel;
        this.last = new HashSet<>();
        last.forEach(graphOrNodeSet -> this.last.add(graphOrNodeSet.duplicate()));
        this.edges = new HashMap<>();
        edges.forEach((memoryAccess, memoryAccesses) -> this.edges.put(memoryAccess, new HashSet<>(memoryAccesses)));
        this.reverse = new HashMap<>();
        reverse.forEach((memoryAccess, memoryAccesses) -> this.reverse.put(memoryAccess, new HashSet<>(memoryAccesses)));
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        if(edgeLabel.contains(label)) {
            edges.putIfAbsent(source, new HashSet<>());
            reverse.putIfAbsent(target, new HashSet<>());
            edges.get(source).add(target);
            reverse.get(target).add(source);
        }

        Set<GraphOrNodeSet> lhs = this.source.filterMk(source, target, label, isFinal);
        Set<GraphOrNodeSet> rhs = this.target.filterMk(source, target, label, isFinal);
        return getNextEdges(lhs, rhs, label);
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        if(edgeLabel.contains(label)) {
            edges.get(source).remove(target);
            reverse.get(target).remove(source);
        }
        Set<GraphOrNodeSet> lhs = this.source.filterRm(source, target, label);
        Set<GraphOrNodeSet> rhs = this.target.filterRm(source, target, label);
        return getNextEdges(lhs, rhs, label);
    }

    @Override
    public Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new NextEdge(forEachNodes, forEachVars, forEachThreads, source, target, edgeLabel, last, edges, reverse);
    }

    private Set<GraphOrNodeSet> getNextEdges(Set<GraphOrNodeSet> lhsSet, Set<GraphOrNodeSet> rhsSet, String label) {
        boolean changed = false;
        for (GraphOrNodeSet lhs : lhsSet) {
            if(lhs.isChanged()) {
                changed = true;
                lhs.setChanged(false);
            }
        }
        for (GraphOrNodeSet rhs : rhsSet) {
            if(rhs.isChanged()) {
                changed = true;
                rhs.setChanged(false);
            }
        }
        if(!changed) {
            return last;
        }
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (GraphOrNodeSet lhs : lhsSet) {
            for (GraphOrNodeSet rhs : rhsSet) {
                if(!lhs.isGraph() && !rhs.isGraph()){
                    Graph ret = Graph.empty();
                    for (MemoryAccess t : lhs.getNodeSet()) {
                        for (MemoryAccess t1 : edges.getOrDefault(t, new HashSet<>())) {
                            if(rhs.getNodeSet().contains(t1)) {
                                ret.addEdge(t, t1, false);
                            }
                        }
                    }
                    retSet.add(GraphOrNodeSet.of(ret));
                }
                else {
                    throw new UnsupportedOperationException("Cannot have a graph as a source and/or target");
                }
            }
        }
        return last = retSet;

    }
}