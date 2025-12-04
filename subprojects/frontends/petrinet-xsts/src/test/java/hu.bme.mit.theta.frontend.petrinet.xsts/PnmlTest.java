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

import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.pnml.XMLPnmlToPetrinet;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfig;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.xpath.XPathExpressionException;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.xml.sax.SAXException;

@Disabled("No PNML datasets configured for parameterized test")
public class PnmlTest {
    public String filePath;
    public String targetMarking;
    public String initialMarking;
    public boolean safe;
    public XstsConfigBuilder.Domain domain;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {

                    //                { "src/test/resources/model/pnml/DPhil-10.pnml", "0 0 1 1 0 0
                    // 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0
                    // 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0", "0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1",
                    // true, XstsConfigBuilder.Domain.EXPL},

                    //                { "src/test/resources/model/pnml/DPhil-100.pnml", "0 0 1 1 0 0
                    // 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0
                    // 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0
                    // 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1
                    // 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0
                    // 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0
                    // 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0
                    // 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1
                    // 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0
                    // 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0
                    // 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0
                    // 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1
                    // 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0
                    // 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0
                    // 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0
                    // 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 1
                    // 1 0 0 0 0 0 0 1 0", "0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0
                    // 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0
                    // 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0
                    // 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0
                    // 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0
                    // 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0
                    // 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0
                    // 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0
                    // 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1 0 0 0 0 1 1", true,
                    // XstsConfigBuilder.Domain.EXPL},

                });
    }

    @MethodSource("data")
    @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}")
    public void test(
            String filePath,
            String targetMarking,
            String initialMarking,
            boolean safe,
            XstsConfigBuilder.Domain domain)
            throws IOException,
                    XPathExpressionException,
                    SAXException,
                    ParserConfigurationException {

        initPnmlTest(filePath, targetMarking, initialMarking, safe, domain);

        final Logger logger = new ConsoleLogger(Level.SUBSTEP);

        final PetriNet petriNet = XMLPnmlToPetrinet.parse(filePath, initialMarking);

        XSTS xsts;
        try (InputStream propStream =
                new ByteArrayInputStream(("prop { " + targetMarking + " }").getBytes())) {
            xsts = PetriNetToXSTS.createXSTS(petriNet, propStream);
        }

        final XstsConfig<?, ?, ?> configuration =
                new XstsConfigBuilder(
                                domain,
                                XstsConfigBuilder.Refinement.SEQ_ITP,
                                Z3LegacySolverFactory.getInstance(),
                                Z3LegacySolverFactory.getInstance())
                        .predSplit(XstsConfigBuilder.PredSplit.CONJUNCTS)
                        .maxEnum(250)
                        .initPrec(XstsConfigBuilder.InitPrec.ALLVARS)
                        .logger(logger)
                        .build(xsts);
        final SafetyResult<?, ?> status = configuration.check();
        if (safe) {
            assertTrue(status.isSafe());
        } else {
            assertTrue(status.isUnsafe());
        }
    }

    public void initPnmlTest(
            String filePath,
            String targetMarking,
            String initialMarking,
            boolean safe,
            XstsConfigBuilder.Domain domain) {
        this.filePath = filePath;
        this.targetMarking = targetMarking;
        this.initialMarking = initialMarking;
        this.safe = safe;
        this.domain = domain;
    }
}
