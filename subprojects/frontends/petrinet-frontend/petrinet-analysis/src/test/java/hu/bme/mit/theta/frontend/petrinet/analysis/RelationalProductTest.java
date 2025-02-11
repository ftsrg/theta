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
package hu.bme.mit.theta.frontend.petrinet.analysis;

import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddSignature;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import org.junit.Before;

public final class RelationalProductTest {
    private static final int[] tupleSignature = new int[] {0, 0, 0};

    private MddGraph<Boolean> graph;
    private MddVariableOrder order;
    private MddSignature signature;

    @Before
    public void prepare() {
        System.out.println("Preparing...");
        graph = JavaMddFactory.getDefault().createMddGraph(LatticeDefinition.forSets());
        order = JavaMddFactory.getDefault().createMddVariableOrder(graph);
        for (int i = 0; i < tupleSignature.length; i++) {
            order.createOnTop(
                    MddVariableDescriptor.create(
                            "x" + i, tupleSignature[tupleSignature.length - i - 1]));
        }
        signature = order.getDefaultSetSignature();
    }
}
