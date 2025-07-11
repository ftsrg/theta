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

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddAnalysisStatistics;
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.pnml.XMLPnmlToPetrinet;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.hu.bme.mit.theta.xsts.analysis.XstsToMonolithicExprKt;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.List;
import org.junit.Test;

public class PnmlSymbolicGSATTest {

    @Test
    public void testPnmlSymbolicGSAT() throws Exception {

        final Logger logger = new ConsoleLogger(Logger.Level.SUBSTEP);

        final PetriNet petriNet =
                XMLPnmlToPetrinet.parse("src/test/resources/pnml/Philosophers-10.pnml", "");

        XSTS xsts;
        try (InputStream propStream = new ByteArrayInputStream(("prop { true }").getBytes())) {
            xsts = PetriNetToXSTS.createXSTS(petriNet, propStream);
        }

        final SafetyResult<?, ?> status;
        try (var solverPool = new SolverPool(Z3LegacySolverFactory.getInstance())) {
            var monolithicExpr = XstsToMonolithicExprKt.toMonolithicExpr(xsts);
            var checker =
                    MddChecker.create(
                            monolithicExpr,
                            List.copyOf(monolithicExpr.getVars()),
                            solverPool,
                            logger,
                            MddChecker.IterationStrategy.GSAT,
                            valuation -> monolithicExpr.getValToState().invoke(valuation),
                            (Valuation v1, Valuation v2) ->
                                    monolithicExpr.getBiValToAction().invoke(v1, v2),
                            true);
            status = checker.check();
            logger.mainStep(
                    "State space size: "
                            + ((MddAnalysisStatistics) status.getStats().get())
                                    .getStateSpaceSize());
        }
    }
}
