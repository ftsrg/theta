package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Process;

import java.util.HashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class ForEachThread<T extends MemoryAccess, L> extends Filter<T, L> {
    private Filter<T, L> op;
    private final Set<Process> processes;
    private Process currentProcess;

    public ForEachThread() {
        processes = new HashSet<>();
        currentProcess = null;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterMk(T source, T target, L label, boolean isFinal) {
        checkState(op != null, "Set the operand before use!");
        processes.add(source.getProcess());
        processes.add(target.getProcess());
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (Process process : processes) {
            currentProcess = process;
            retSet.addAll(op.filterMk(source, target, label, isFinal));
        }
        return retSet;
    }

    @Override
    public Set<GraphOrNodeSet<T>> filterRm(T source, T target, L label) {
        checkState(op != null, "Set the operand before use!");
        processes.add(source.getProcess());
        processes.add(target.getProcess());
        Set<GraphOrNodeSet<T>> retSet = new HashSet<>();
        for (Process process : processes) {
            currentProcess = process;
            retSet.addAll(op.filterRm(source, target, label));
        }
        return retSet;
    }

    public void setOp(Filter<T, L> op) {
        this.op = op;
    }

    public Process getCurrentProcess() {
        return currentProcess;
    }
}