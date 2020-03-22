/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Stack;

/**
 * Stores every (static and runtime) structure of a process
 * A call stack is used for handling recursion.
 */
final class ProcessState {
	private final Stack<CallState> callStack;
	private final XCFA.Process process;
	private final ExplState parent;

	ProcessState(ExplState parent, XCFA.Process process) {
		this.parent = parent;
		callStack = new Stack<>();
		this.process = process;
		push(process.getMainProcedure(), new ArrayList<>(), null);
	}

	ProcessState(ExplState stepParent, ProcessState toCopy) {
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
		callStack.push(new CallState(this, ProcedureData.getInstance(procedure, process), params, resultVar));
	}

	public void push(XCFA.Process.Procedure procedure, List<VarDecl<?>> params) {
		callStack.push(new CallState(this, ProcedureData.getInstance(procedure, process), params));
	}

	void collectEnabledTransitions(Collection<Transition> transitions) {
		// process has finished
		if (callStack.empty())
			return;
		callStack.peek().collectEnabledTransitions(transitions);
	}

	ExplState getExplState() {
		return parent;
	}

	CallState getCallStackPeek() {
		return callStack.peek();
	}

	public boolean isFinished() {
		return callStack.empty();
	}

	public boolean isSafe() {
		// if there is callstack is already empty...
		if (isFinished())
			return true;
		return getCallStackPeek().isSafe();
	}

	public XCFA.Process getProcess() {
		return process;
	}
}
