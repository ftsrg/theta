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

import static org.junit.Assert.assertEquals;

import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SimpleSaturationProvider;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.pnml.PetriNetParser;
import java.io.File;
import java.util.List;
import org.junit.jupiter.api.Test;

public final class SimpleSaturationTest {
    public static String reverseString(String str) {
        StringBuilder sb = new StringBuilder(str);
        sb.reverse();
        return sb.toString();
    }

    @Test
    public void testSS() throws Exception {
        final File pnmlFile = new File(getClass().getResource(TestData.MODELPATH).toURI());
        final List<PetriNet> petriNets = PetriNetParser.loadPnml(pnmlFile).parsePTNet();

        assertEquals(1, petriNets.size());

        final List<Place> ordering =
                VariableOrderingFactory.fromPathString(
                        getClass().getResource(TestData.ORDERINGPATH).toURI().getPath(),
                        petriNets.get(0));
        // 	ordering = new ArrayList<>(petriNets.get(0).getPlaces());
        // ordering.sort((p1, p2) ->
        // String.CASE_INSENSITIVE_ORDER.compare(reverseString(p1.getId()),
        //  	reverseString(p2.getId())));
        // ordering.sort((p1, p2) -> String.CASE_INSENSITIVE_ORDER.compare(p1.getId(),
        //	p2.getId()));

        PtNetSystem system = new PtNetSystem(petriNets.get(0), ordering);

        System.out.println(system.printDependencyMatrixCsv());

        // new BufferedReader(new InputStreamReader(System.in)).readLine();

        MddVariableOrder variableOrder =
                JavaMddFactory.getDefault().createMddVariableOrder(LatticeDefinition.forSets());
        for (Place p : ordering) {
            variableOrder.createOnTop(MddVariableDescriptor.create(p));
        }

        SimpleSaturationProvider ss = new SimpleSaturationProvider(variableOrder);

        final MddHandle stateSpace =
                ss.compute(
                        system.getInitializer(),
                        system.getTransitions(),
                        variableOrder.getDefaultSetSignature().getTopVariableHandle());

        // String dot = GraphvizSerializer.serialize(stateSpace);
        // System.out.println(dot);

        System.out.println(ss.getSaturatedNodes().size());

        // StringSelection stringSelection = new StringSelection(dot);
        // Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
        // clipboard.setContents(stringSelection, null);

        final Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace);
        assertEquals(TestData.STATESPACESIZE, stateSpaceSize.longValue());
        System.out.println("Size of state space: " + stateSpaceSize);
    }
}
