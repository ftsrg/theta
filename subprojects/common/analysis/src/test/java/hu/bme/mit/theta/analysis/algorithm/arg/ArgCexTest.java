/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.stubs.ActionStub;
import hu.bme.mit.theta.analysis.stubs.PartialOrdStub;
import hu.bme.mit.theta.analysis.stubs.StateStub;
import org.junit.Assert;
import org.junit.Test;

import java.util.List;
import java.util.stream.Collectors;

public class ArgCexTest {

    @Test
    public void test() {
        final ARG<State, Action> arg = ARG.create(new PartialOrdStub());

        final State s1 = new StateStub("S1");
        final State s2 = new StateStub("S2");
        final State s3 = new StateStub("S3");
        final State s4 = new StateStub("S4");
        final State s5 = new StateStub("S5");
        final State s6 = new StateStub("S6");
        final State s7 = new StateStub("S7");
        final State s8 = new StateStub("S8");

        final Action act = new ActionStub("A");

        final ArgNode<State, Action> n1 = arg.createInitNode(s1, false);
        final ArgNode<State, Action> n2 = arg.createSuccNode(n1, act, s2, false);
        final ArgNode<State, Action> n3 = arg.createSuccNode(n1, act, s3, false);
        final ArgNode<State, Action> n4 = arg.createSuccNode(n2, act, s4, true);
        final ArgNode<State, Action> n5 = arg.createSuccNode(n2, act, s5, false);
        final ArgNode<State, Action> n6 = arg.createSuccNode(n3, act, s6, false);
        @SuppressWarnings("unused") final ArgNode<State, Action> n7 = arg.createSuccNode(n3, act,
                s7, true);
        final ArgNode<State, Action> n8 = arg.createSuccNode(n5, act, s8, true);

        n6.setCoveringNode(n2);
        n8.setCoveringNode(n4);

        Assert.assertEquals(8, arg.getNodes().count());
        Assert.assertEquals(2, arg.getUnsafeNodes().count());

        final List<Trace<State, Action>> cexs = arg.getCexs().map(e -> e.toTrace())
                .collect(Collectors.toList());

        Assert.assertEquals(2, cexs.size());
        Assert.assertTrue(
                cexs.contains(Trace.of(ImmutableList.of(s1, s2, s4), ImmutableList.of(act, act))));
        Assert.assertTrue(
                cexs.contains(Trace.of(ImmutableList.of(s1, s3, s7), ImmutableList.of(act, act))));

    }
}
