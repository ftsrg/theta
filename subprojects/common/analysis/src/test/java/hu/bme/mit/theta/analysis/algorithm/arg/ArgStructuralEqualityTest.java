/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.arg;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.stubs.ActionStub;
import hu.bme.mit.theta.analysis.stubs.PartialOrdStub;
import hu.bme.mit.theta.analysis.stubs.StateStub;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class ArgStructuralEqualityTest {

    private static ARG<State, Action> createArg(boolean variant) {
        ARG<State, Action> arg = ARG.create(new PartialOrdStub());
        Action act = new ActionStub("A");

        ArgNode<State, Action> s0 = arg.createInitNode(new StateStub("s0"), false);
        ArgNode<State, Action> s10 = arg.createSuccNode(s0, act, new StateStub("s10"), false);
        ArgNode<State, Action> s20 = arg.createSuccNode(s10, act, new StateStub("s20"), true);
        ArgNode<State, Action> s21 = arg.createSuccNode(s10, act, new StateStub("s21"), false);
        ArgNode<State, Action> s11 = arg.createSuccNode(s0, act, new StateStub("s11"), true);
        if (variant) {
            ArgNode<State, Action> s12a = arg.createSuccNode(s0, act, new StateStub("s12a"), false);
        } else {
            ArgNode<State, Action> s12b = arg.createSuccNode(s0, act, new StateStub("s12b"), false);
        }
        return arg;
    }

    @Test
    public void testARGEquals() {
        var arg1 = createArg(true);
        var arg2 = createArg(true);
        var arg3 = createArg(false);

        Assertions.assertNotEquals(arg1, arg2, "Reference-based equality");
        Assertions.assertTrue(
                ArgStructuralEquality.equals(arg1, arg2), "Structural equality (true)");
        Assertions.assertFalse(
                ArgStructuralEquality.equals(arg1, arg3), "Structural equality (false)");
    }

    @Test
    public void testARGHashCode() {
        var arg1 = createArg(true);
        var arg2 = createArg(true);
        var arg3 = createArg(false);

        Assertions.assertNotEquals(arg1.hashCode(), arg2.hashCode(), "Reference-based hashcode");
        Assertions.assertEquals(
                ArgStructuralEquality.hashCode(arg1),
                ArgStructuralEquality.hashCode(arg2),
                "Structural hashcode (true)");
        Assertions.assertNotEquals(
                ArgStructuralEquality.hashCode(arg1),
                ArgStructuralEquality.hashCode(arg3),
                "Structural hashcode (false)");
    }
}
