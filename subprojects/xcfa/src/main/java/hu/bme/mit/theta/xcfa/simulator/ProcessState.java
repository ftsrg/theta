package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Stack;

public class ProcessState {
	private Stack<CallState> callStack;
	private XCFA.Process process;
	private RuntimeState parent;

	public ProcessState(RuntimeState parent, XCFA.Process process) {
		this.parent = parent;
		callStack = new Stack<>();
		this.process = process;
		push(process.getMainProcedure(), new ArrayList<>(), null);
	}

	public ProcessState(RuntimeState stepParent, ProcessState toCopy) {
		process = toCopy.process; // no need to copy static structure
		parent = stepParent;
		callStack = new Stack<>();
		for (CallState c : toCopy.callStack) {
			callStack.push(new CallState(this, c));
		}
	}

	public void pop() {
		callStack.pop();
	}

	public void push(XCFA.Process.Procedure procedure, List<VarDecl<?>> params, VarDecl<?> resultVar) {
		callStack.push(new CallState(this, new ProcedureData(procedure), params, resultVar));
	}

	public void push(XCFA.Process.Procedure procedure, List<VarDecl<?>> params) {
		callStack.push(new CallState(this, new ProcedureData(procedure), params));
	}

	public void collectEnabledTransitions(RuntimeState x, Collection<Transition> transitions) {
		// process has finished
		if (callStack.empty())
			return;
		callStack.peek().collectEnabledTransitions(x, transitions);
	}

	public RuntimeState getRuntimeState() {
		return parent;
	}

	public CallState getCallStackPeek() {
		return callStack.peek();
	}

	public XCFA.Process getProcess() {
		return process;
	}

	public boolean isFinished() {
		return callStack.empty();
	}
}
