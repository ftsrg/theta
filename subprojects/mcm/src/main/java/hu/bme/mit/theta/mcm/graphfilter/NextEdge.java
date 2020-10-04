package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class NextEdge<T extends MemoryAccess> extends Filter<T> {
    private final Filter<T> source;
    private final Filter<T> target;
    private final String edgeLabel;
    private Set<GraphOrNodeSet<T>> last;
    private final Map<T, Set<T>> edges;
    private final Map<T, Set<T>> reverse;


    public NextEdge(Filter<T> source, Filter<T> target, String edgeLabel) {
        this.source = source;
        this.target = target;
        this.edgeLabel = edgeLabel;
        this.last = new HashSet<>();
        edges = new HashMap<>();
        reverse = new HashMap<>();
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        if(!label.equals(edgeLabel)) {
            return last;
        }
        else {
            edges.putIfAbsent(source, new HashSet<>());
            reverse.putIfAbsent(target, new HashSet<>());

            edges.get(source).add(target);
            reverse.get(target).add(source);
            Set<GraphOrNodeSet<T>> lhs = this.source.filterMk(source, target, label, isFinal);
            Set<GraphOrNodeSet<T>> rhs = this.target.filterMk(source, target, label, isFinal);
            return getNextEdges(lhs, rhs, label);
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
            edges.get(source).remove(target);
            reverse.get(target).remove(source);
            Set<GraphOrNodeSet<T>> lhs = this.source.filterRm(source, target, label);
            Set<GraphOrNodeSet<T>> rhs = this.target.filterRm(source, target, label);
            return getNextEdges(lhs, rhs, label);
        }
    }

    private Set<GraphOrNodeSet<T>> getNextEdges(Set<GraphOrNodeSet<T>> lhsSet, Set<GraphOrNodeSet<T>> rhsSet, String label) {
        boolean changed = false;
        for (GraphOrNodeSet<T> lhs : lhsSet) {
            if(lhs.isChanged()) {
                changed = true;
                lhs.setChanged(false);
            }
        }
        for (GraphOrNodeSet<T> rhs : rhsSet) {
            if(rhs.isChanged()) {
                changed = true;
                rhs.setChanged(false);
            }
        }
        if(!changed) {
            return last;
        }
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (GraphOrNodeSet<T> lhs : lhsSet) {
            for (GraphOrNodeSet<T> rhs : rhsSet) {
                if(!lhs.isChanged() && !rhs.isChanged()) {
                    return last;
                }
                else if(!lhs.isGraph() && !rhs.isGraph()){
                    Graph<T> ret = Graph.create(false);
                    for (T t : lhs.getNodeSet()) {
                        for (T t1 : edges.get(t)) {
                            ret.addEdge(t, t1, false);
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