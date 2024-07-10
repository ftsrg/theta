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
package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.symbolic.checker.MddCex;
import hu.bme.mit.theta.analysis.algorithm.symbolic.checker.MddChecker;
import hu.bme.mit.theta.analysis.algorithm.symbolic.checker.MddWitness;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.sts.STS;
import hu.bme.mit.theta.sts.aiger.AigerParser;
import hu.bme.mit.theta.sts.aiger.AigerToSts;
import hu.bme.mit.theta.sts.analysis.config.StsConfig;
import hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder;
import hu.bme.mit.theta.sts.dsl.StsDslManager;
import hu.bme.mit.theta.sts.dsl.StsSpec;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import static hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.Domain.EXPL;
import static hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.Domain.PRED_CART;
import static hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.Refinement.SEQ_ITP;
import static org.junit.Assert.assertTrue;

@RunWith(value = Parameterized.class)
public class StsMddCheckerTest {
    @Parameterized.Parameter(value = 0)
    public String filePath;

    @Parameterized.Parameter(value = 1)
    public boolean safe;

    @Parameterized.Parameters(name = "{index}: {0}, {1}")
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{
                {"src/test/resources/hw1_false.aag", false},

                {"src/test/resources/hw2_true.aag", true},

                {"src/test/resources/boolean1.system", false},

                {"src/test/resources/boolean2.system", false},

                {"src/test/resources/counter.system", true},

                {"src/test/resources/counter_bad.system", false},

                {"src/test/resources/counter_parametric.system", true},

                {"src/test/resources/loop.system", true},

                {"src/test/resources/loop_bad.system", false},

                {"src/test/resources/multipleinitial.system", false},

                {"src/test/resources/readerswriters.system", true},

                {"src/test/resources/simple1.system", false},

                {"src/test/resources/simple2.system", true},

                {"src/test/resources/simple3.system", false},
        });
    }

    @Test
    public void test() throws IOException {
        final Logger logger = new ConsoleLogger(Logger.Level.SUBSTEP);

        final STS sts;
        if (filePath.endsWith("aag")) sts = AigerToSts.createSts(AigerParser.parse(filePath));
        else {
            final StsSpec spec = StsDslManager.createStsSpec(new FileInputStream(filePath));
            if (spec.getAllSts().size() != 1)
                throw new UnsupportedOperationException("STS contains multiple properties.");
            sts = Utils.singleElementOf(spec.getAllSts());
        }
        final MddChecker<ExprAction> checker = MddChecker.create(sts.getInit(), VarIndexingFactory.indexing(0), new ExprAction() {
            @Override
            public Expr<BoolType> toExpr() {
                return sts.getTrans();
            }

            @Override
            public VarIndexing nextIndexing() {
                return VarIndexingFactory.indexing(1);
            }
        }, sts.getProp(), Z3SolverFactory.getInstance(), logger);

        final SafetyResult<MddWitness, MddCex> status = checker.check(null);
        if (safe) {
            assertTrue(status.isSafe());
        } else {
            assertTrue(status.isUnsafe());
        }
    }

}
