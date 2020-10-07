package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Process;

import java.util.*;

public class ForEachThread extends Filter {
    private final Map<Process, Filter> op;
    private final List<? extends Process> processes;
    private Process currentProcess;

    public ForEachThread(List<? extends Process> processes) {
        this.processes = processes;
        currentProcess = null;
        op = new HashMap<>();
    }

    public ForEachThread(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads, Map<Process, Filter> op, List<? extends Process> processes, Process currentProcess) {
        forEachThreads.push(this);
        this.op = new HashMap<>();
        op.forEach((process, filter) -> this.op.put(process, filter.duplicate(forEachNodes, forEachVars, forEachThreads)));
        this.processes = processes;
        this.currentProcess = currentProcess;
        forEachThreads.pop();
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (Process process : processes) {
            currentProcess = process;
            retSet.addAll(op.get(currentProcess).filterMk(source, target, label, isFinal));
        }
        return retSet;
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (Process process : processes) {
            currentProcess = process;
            retSet.addAll(op.get(currentProcess).filterRm(source, target, label));
        }
        return retSet;
    }

    @Override
    protected Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new ForEachThread(forEachNodes, forEachVars, forEachThreads, op, processes, currentProcess);
    }

    public void setOp(Filter op) {
        Stack<ForEachThread> forEachThreads = new Stack<>();
        forEachThreads.push(this);
        for (Process process : processes) {
            this.op.put(process, op.duplicate(new Stack<>(), new Stack<>(), forEachThreads));
        }
    }

    public Process getCurrentProcess() {
        return currentProcess;
    }
}