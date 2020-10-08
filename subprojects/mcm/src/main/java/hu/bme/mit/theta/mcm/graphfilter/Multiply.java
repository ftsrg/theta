package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.Graph;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

public class Multiply extends Filter {
    private final Filter lhs;
    private final Filter rhs;
    private Set<GraphOrNodeSet> last;

    public Multiply(Filter lhs, Filter rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.last = new HashSet<>();
    }

    public Multiply(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads, Filter lhs, Filter rhs, Set<GraphOrNodeSet> last) {
            this.lhs = lhs.duplicate(forEachNodes, forEachVars, forEachThreads);
            this.rhs = rhs.duplicate(forEachNodes, forEachVars, forEachThreads);
            this.last = new HashSet<>();
            last.forEach(graphOrNodeSet -> this.last.add(graphOrNodeSet.duplicate()));
        }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {

        Set<GraphOrNodeSet> lhs = this.lhs.filterMk(source, target, label, isFinal);
        Set<GraphOrNodeSet> rhs = this.rhs.filterMk(source, target, label, isFinal);
        return getMultiplication(lhs, rhs);
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        Set<GraphOrNodeSet> lhs = this.lhs.filterRm(source, target, label);
        Set<GraphOrNodeSet> rhs = this.rhs.filterRm(source, target, label);
        return getMultiplication(lhs, rhs);
    }

    @Override
    public Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new Multiply(forEachNodes, forEachVars, forEachThreads, lhs, rhs, last);
    }

    private Set<GraphOrNodeSet> getMultiplication(Set<GraphOrNodeSet> lhsSet, Set<GraphOrNodeSet> rhsSet) {
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
                if(lhs.isGraph() || rhs.isGraph()) {
                    throw new UnsupportedOperationException("Cannot multiply graphs!");
                }
                else {
                    Graph ret = Graph.empty();
                    for (MemoryAccess t : lhs.getNodeSet()) {
                        for (MemoryAccess t1 : rhs.getNodeSet()) {
                            ret.addEdge(t, t1, false);
                        }
                    }
                    retSet.add(GraphOrNodeSet.of(ret));
                }
            }
        }
        return last = retSet;

    }

}
