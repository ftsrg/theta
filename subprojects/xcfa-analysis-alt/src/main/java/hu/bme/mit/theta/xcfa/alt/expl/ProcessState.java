/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.*;

final class ProcessState {
    private final Stack<CallState> callStack;

    public ProcessState(Stack<CallState> callStack) {
        this.callStack = callStack;
    }

    public static ProcessState copyOf(ProcessState processState, ExplState.Factory0 factory) {
        Stack<CallState> callStack = new Stack<>();
        processState.callStack.stream().map(
                p -> factory.createCallState(p.getProcess(), p.getProcedure(), p.getLocation(), p.getCallerResultVar())
        ).forEach(callStack::add);
        return new ProcessState(callStack);
    }

    CallState getActiveCallState() {
        return callStack.peek();
    }

    public static ProcessState initial(XCFA.Process process, ExplState.Factory0 factory) {
        Stack<CallState> callStack = new Stack<>();
        callStack.add(CallState.initial(process, factory));
        return new ProcessState(callStack);
    }

    public boolean isFinal() {
        return SafetyUtils.getSafety(this).isFinished();
    }

    public void push(CallState callState) {
        callStack.add(callState);
    }

    public void pop() {
        callStack.pop();
    }

    public int getCallStackSize() {
        return callStack.size();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ProcessState that = (ProcessState) o;
        return callStack.equals(that.callStack);
    }

    @Override
    public int hashCode() {
        return Objects.hash(callStack);
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder("ProcessState").add(callStack).toString();
    }
}
