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
package hu.bme.mit.theta.sts.analysis;

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

import hu.bme.mit.theta.analysis.algorithm.ic3.Ic3Checker;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.sts.STS;
import hu.bme.mit.theta.sts.aiger.AigerParser;
import hu.bme.mit.theta.sts.aiger.AigerToSts;
import hu.bme.mit.theta.sts.analysis.pipeline.StsPipelineChecker;
import hu.bme.mit.theta.sts.dsl.StsDslManager;
import hu.bme.mit.theta.sts.dsl.StsSpec;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class StsIc3Test {
    public String filePath;
    public boolean isSafe;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"src/test/resources/hw1_false.aag", false},
                    {"src/test/resources/hw2_true.aag", true},
                    {"src/test/resources/boolean1.system", false},
                    {"src/test/resources/boolean2.system", false},
                    {"src/test/resources/counter.system", true},
                    {"src/test/resources/counter_bad.system", false},
                    {"src/test/resources/counter_parametric.system", true},

                    //                {"src/test/resources/loop.system", true},

                    {"src/test/resources/loop_bad.system", false},
                    {"src/test/resources/multipleinitial.system", false},
                    {"src/test/resources/readerswriters.system", true},
                    {"src/test/resources/simple1.system", false},
                    {"src/test/resources/simple2.system", true},
                    {"src/test/resources/simple3.system", false},
                });
    }

    @MethodSource("data")
    @ParameterizedTest(name = "{index}: {0}, {1}")
    public void testIC3(String filePath, boolean isSafe) throws IOException {

        initStsIc3Test(filePath, isSafe);

        final Logger logger = new ConsoleLogger(Logger.Level.VERBOSE);

        final STS sts;
        if (filePath.endsWith("aag")) {
            sts = AigerToSts.createSts(AigerParser.parse(filePath));
        } else {
            final StsSpec spec = StsDslManager.createStsSpec(new FileInputStream(filePath));
            if (spec.getAllSts().size() != 1) {
                throw new UnsupportedOperationException("STS contains multiple properties.");
            }
            sts = Utils.singleElementOf(spec.getAllSts());
        }

        final var checker =
                new StsPipelineChecker<>(
                        sts,
                        monolithicExpr ->
                                new Ic3Checker(
                                        monolithicExpr,
                                        Z3LegacySolverFactory.getInstance(),
                                        true,
                                        true,
                                        true,
                                        true,
                                        true,
                                        true,
                                        logger),
                        List.of(),
                        List.of(),
                        logger);
        Assertions.assertEquals(isSafe, checker.check().isSafe());
    }

    public void initStsIc3Test(String filePath, boolean isSafe) {
        this.filePath = filePath;
        this.isSafe = isSafe;
    }
}
