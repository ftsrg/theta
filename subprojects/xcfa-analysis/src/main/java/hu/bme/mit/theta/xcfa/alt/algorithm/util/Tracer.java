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
package hu.bme.mit.theta.xcfa.alt.algorithm.util;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.xcfa.alt.expl.ExplState;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

// TODO rename
public class Tracer {

    private Tracer() { }

    private static final ARG<ExplState, Transition> arg = ARG.create(Object::equals);

    public static Trace<ExplState, Transition> createTrace(Stack<? extends DfsNodeInterface> dfsStack) {

        List<ExplState> states = new ArrayList<>();
        List<Transition> actions = new ArrayList<>();

        for (DfsNodeInterface t: dfsStack) {
            states.add(t.getState());
            if (t.getLastTransition() != null) {
                actions.add(t.getLastTransition());
            }
        }
        return Trace.of(states, actions);
    }

    public static SafetyResult.Safe<ExplState, Transition> safe() {
        return SafetyResult.safe(arg);
    }

    public static SafetyResult.Unsafe<ExplState, Transition> unsafe(Stack<? extends DfsNodeInterface> dfsStack) {
        return SafetyResult.unsafe(createTrace(dfsStack), arg);
    }
}
