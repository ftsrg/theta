package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class ForEachNode<T extends MemoryAccess, L> extends Filter<T, L> {
    private final Filter<T, L> pattern;
    private Filter<T, L> op;
    private T currentNode;

    public ForEachNode(Filter<T, L> pattern) {
        this.pattern = pattern;
        this.currentNode = null;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        checkState(op != null, "Set the operand before use!");
        Set<GraphOrNodeSet<T>> patterns = pattern.filterMk(source, target, label, isFinal);
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (GraphOrNodeSet<T> pattern : patterns) {
            checkState(!pattern.isGraph(),"Cannot iterate over the nodes of a graph!");
            for (T node : pattern.getNodeSet()) {
                currentNode = node;
                retSet.addAll(op.filterMk(source, target, label, isFinal));
            }
        }
        return retSet;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label){
        checkState(op != null, "Set the operand before use!");
        Set<GraphOrNodeSet<T>> patterns = pattern.filterRm(source, target, label);
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (GraphOrNodeSet<T> pattern : patterns) {
            checkState(!pattern.isGraph(),"Cannot iterate over the nodes of a graph!");
            for (T node : pattern.getNodeSet()) {
                currentNode = node;
                retSet.addAll(op.filterRm(source, target, label));
            }
        }
        return retSet;
    }

    public void setOp(Filter<T, L> op) {
        this.op = op;
    }

    public T getCurrentNode() {
        return currentNode;
    }
}
