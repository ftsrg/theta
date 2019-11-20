package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

class ProcessState {
    Stack<CallState> callStack;
    XCFA.Process process;
    RuntimeState parent;

    public ProcessState(RuntimeState parent, XCFA.Process process) {
        this.parent = parent;
        callStack = new Stack<>();
        this.process = process;
        push(process.getMainProcedure(), new ArrayList<>(), null);
    }

    public void pop() {
        callStack.pop();
    }

    public boolean step() {
        if (callStack.empty())
            return false;
        return callStack.peek().step();
    }

    public void push(XCFA.Process.Procedure procedure, List<VarDecl<?>> params, VarDecl<?> resultVar) {
        callStack.push(new CallState(this, procedure, params, resultVar));
    }

    public void push(XCFA.Process.Procedure procedure, List<VarDecl<?>> params) {
        callStack.push(new CallState(this, procedure, params));
    }
}
