package hu.bme.mit.theta.mcm.graphfilter;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.mcm.GraphOrNodeSet;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.*;

public class ForEachVar extends Filter{
    private Map<VarDecl<?>, Filter> op;
    private final List<VarDecl<? extends Type>> variables;
    private VarDecl<?> currentVariable;

    public ForEachVar(List<VarDecl<? extends Type>> variables) {
        this.variables = variables;
        currentVariable = null;
    }

    public ForEachVar(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads, Map<VarDecl<?>, Filter> op, List<VarDecl<? extends Type>> variables, VarDecl<?> currentVariable) {
        forEachVars.push(this);
        this.op = new HashMap<>();
        op.forEach((variable, filter) -> this.op.put(variable, filter.duplicate(forEachNodes, forEachVars, forEachThreads)));
        this.variables = variables;
        this.currentVariable = currentVariable;
        forEachVars.pop();
    }

    @Override
    public Set<GraphOrNodeSet> filterMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        variables.add(source.getGlobalVariable());
        variables.add(target.getGlobalVariable());
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (VarDecl<?> variable : variables) {
            currentVariable = variable;
            retSet.addAll(op.get(variable).filterMk(source, target, label, isFinal));
        }
        return retSet;
    }

    @Override
    public Set<GraphOrNodeSet> filterRm(MemoryAccess source, MemoryAccess target, String label) {
        variables.add(source.getGlobalVariable());
        variables.add(target.getGlobalVariable());
        Set<GraphOrNodeSet> retSet = new HashSet<>();
        for (VarDecl<?> variable : variables) {
            currentVariable = variable;
            retSet.addAll(op.get(variable).filterRm(source, target, label));
        }
        return retSet;
    }

    @Override
    public Filter duplicate(Stack<ForEachNode> forEachNodes, Stack<ForEachVar> forEachVars, Stack<ForEachThread> forEachThreads) {
        return new ForEachVar(forEachNodes, forEachVars, forEachThreads, op, variables, currentVariable);
    }

    public void setOp(Filter op) {
        Stack<ForEachVar> forEachVars = new Stack<>();
        for (VarDecl<?> variable : variables) {
            this.op.put(variable, op.duplicate(new Stack<>(), forEachVars, new Stack<>()));
        }
    }

    public VarDecl<?> getCurrentVariable() {
        return currentVariable;
    }
}
