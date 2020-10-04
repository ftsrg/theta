package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Variable;

import java.util.HashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class ForEachVar<T extends MemoryAccess> extends Filter<T>{
    private Filter<T> op;
    private final Set<Variable> variables;
    private Variable currentVariable;

    public ForEachVar() {
        variables = new HashSet<>();
        currentVariable = null;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, String label, boolean isFinal) {
        checkState(op != null, "Set the operand before use!");
        variables.add(source.getGlobalVariable());
        variables.add(target.getGlobalVariable());
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (Variable variable : variables) {
            currentVariable = variable;
            retSet.addAll(op.filterMk(source, target, label, isFinal));
        }
        return retSet;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, String label) {
        checkState(op != null, "Set the operand before use!");
        variables.add(source.getGlobalVariable());
        variables.add(target.getGlobalVariable());
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (Variable variable : variables) {
            currentVariable = variable;
            retSet.addAll(op.filterRm(source, target, label));
        }
        return retSet;
    }

    public void setOp(Filter<T> op) {
        this.op = op;
    }

    public Variable getCurrentVariable() {
        return currentVariable;
    }
}
