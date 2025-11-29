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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg;

import static org.mockito.Mockito.mock;

import hu.bme.mit.theta.analysis.algorithm.asg.ASGEdge;
import hu.bme.mit.theta.analysis.algorithm.asg.ASGNode;
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import java.util.List;
import org.junit.Assert;
import org.junit.jupiter.api.Test;
import org.junit.runner.RunWith;
import org.mockito.junit.MockitoJUnitRunner;

@RunWith(MockitoJUnitRunner.class)
public class ASGTraceTest {

    @Test
    public void testSimpleLasso() {
        ASGNode<ExprState, ExprAction> initNode = new ASGNode<>(mock(ExprState.class), false);
        ASGNode<ExprState, ExprAction> hondaNode = new ASGNode<>(mock(ExprState.class), true);
        ASGNode<ExprState, ExprAction> loopNode = new ASGNode<>(mock(ExprState.class), false);
        Assert.assertNotEquals(initNode, hondaNode);
        Assert.assertNotEquals(initNode, loopNode);
        Assert.assertNotEquals(loopNode, hondaNode);
        ASGEdge<ExprState, ExprAction> firstEdge =
                new ASGEdge<>(initNode, hondaNode, mock(ExprAction.class), false);
        ASGEdge<ExprState, ExprAction> secondEdge =
                new ASGEdge<>(hondaNode, loopNode, mock(ExprAction.class), false);
        ASGEdge<ExprState, ExprAction> thirdEdge =
                new ASGEdge<>(loopNode, hondaNode, mock(ExprAction.class), false);
        initNode.addOutEdge(firstEdge);
        hondaNode.addInEdge(firstEdge);
        hondaNode.addOutEdge(secondEdge);
        loopNode.addInEdge(secondEdge);
        loopNode.addOutEdge(thirdEdge);
        hondaNode.addInEdge(thirdEdge);

        ASGTrace<ExprState, ExprAction> trace =
                new ASGTrace<>(List.of(firstEdge, secondEdge, thirdEdge), hondaNode);

        Assert.assertEquals(1, trace.getTail().size());
        Assert.assertEquals(2, trace.getLoop().size());
        Assert.assertEquals(initNode, trace.getTail().get(0).getSource());
        Assert.assertEquals(hondaNode, trace.getTail().get(0).getTarget());
        Assert.assertEquals(hondaNode, trace.getLoop().get(0).getSource());
        Assert.assertEquals(loopNode, trace.getLoop().get(0).getTarget());
        Assert.assertEquals(loopNode, trace.getLoop().get(1).getSource());
        Assert.assertEquals(hondaNode, trace.getLoop().get(1).getTarget());
    }
}
