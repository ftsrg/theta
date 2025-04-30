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
package hu.bme.mit.theta.frontend.petrinet.xsts;

import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddAnalysisStatistics;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.pnml.XMLPnmlToPetrinet;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.mdd.XstsMddChecker;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import org.junit.Test;

public class PnmlSymbolicGSATTest {

    @Test
    public void testPnmlSymbolicGSAT() throws Exception {

        final Logger logger = new ConsoleLogger(Logger.Level.SUBSTEP);

        final PetriNet petriNet =
                XMLPnmlToPetrinet.parse("src/test/resources/pnml/Philosophers-5.pnml", "");

        XSTS xsts;
        try (InputStream propStream = new ByteArrayInputStream(("prop { true }").getBytes())) {
            xsts = PetriNetToXSTS.createXSTS(petriNet, propStream);
        }

        final SafetyResult<?, ?> status;
        try (var solverPool = new SolverPool(Z3LegacySolverFactory.getInstance())) {
            final SafetyChecker<?, ?, ?> checker = XstsMddChecker.create(xsts, solverPool, logger);
            status = checker.check();
            logger.mainStep(
                    "State space size: "
                            + ((MddAnalysisStatistics) status.getStats().get())
                                    .getStateSpaceSize());
        }
    }
}
