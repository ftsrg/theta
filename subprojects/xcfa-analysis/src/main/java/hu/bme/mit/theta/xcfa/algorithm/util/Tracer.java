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
package hu.bme.mit.theta.xcfa.algorithm.util;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.xcfa.expl.ExplState;
import hu.bme.mit.theta.xcfa.expl.Transition;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class Tracer {

    public static class TransitionAction implements Action {
        Transition t;
        TransitionAction(Transition t) {
            this.t = t;
        }

        @Override
        public String toString() {
            return t.toString();
        }
    }

    public static Trace<ExplState, TransitionAction> createTrace(Stack<? extends DfsNodeInterface> dfsStack) {

        List<ExplState> states = new ArrayList<>();
        List<TransitionAction> actions = new ArrayList<>();

        for (DfsNodeInterface t: dfsStack) {
            states.add(t.getState());
            if (t.getLastTransition() != null) {
                actions.add(new TransitionAction(t.getLastTransition()));
            }
        }
        return Trace.of(states, actions);
    }

    private static final ARG<ExplState, TransitionAction> arg = ARG.create(Object::equals);

    public static SafetyResult.Safe<ExplState, TransitionAction> safe() {
        return SafetyResult.safe(arg);
    }

    public static SafetyResult.Unsafe<ExplState, TransitionAction> unsafe(Stack<? extends DfsNodeInterface> dfsStack) {
        return SafetyResult.unsafe(createTrace(dfsStack), arg);
    }
}
