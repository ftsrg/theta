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
package hu.bme.mit.theta.analysis.algorithm.loopchecker;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LDGAbstractor;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopcheckerSearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg.LDG;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplStatePredicate;
import hu.bme.mit.theta.analysis.expl.ExplStmtAnalysis;
import hu.bme.mit.theta.analysis.stmtoptimizer.DefaultStmtOptimizer;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaAnalysis;
import hu.bme.mit.theta.cfa.analysis.CfaPrec;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.cfa.analysis.lts.CfaLts;
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsAllVarsInitPrec;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.function.Predicate;
import kotlin.Unit;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class LDGAbstractorCheckingTest {

    @Parameterized.Parameter public String fileName;

    @Parameterized.Parameter(1)
    public String propFileName;

    @Parameterized.Parameter(2)
    public String acceptingLocationName;

    @Parameterized.Parameter(3)
    public boolean isLassoPresent;

    @Parameterized.Parameters
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"counter6to7.cfa", "", "IS6", true},
                    {"counter6to7.xsts", "x_eq_7.prop", "", true},
                    {"counter6to7.xsts", "x_eq_6.prop", "", true},
                    {"infinitehavoc.xsts", "x_eq_7.prop", "", true},
                    {"colors.xsts", "currentColor_eq_Green.prop", "", true},
                    {"counter5.xsts", "x_eq_5.prop", "", true},
                    {"forever5.xsts", "x_eq_5.prop", "", true},
                    {"counter6to7.xsts", "x_eq_5.prop", "", false},
                    {"weather.xsts", "isWet_eq_true.prop", "", false},
                    {"weather.xsts", "waterproof.prop", "", true}
                });
    }

    @Test
    public void test() throws IOException {
        if (propFileName.isBlank() && !acceptingLocationName.isBlank()) testWithCfa();
        if (!propFileName.isBlank() && acceptingLocationName.isBlank()) testWithXsts();
    }

    private void testWithXsts() throws IOException {
        XSTS xsts;
        try (InputStream inputStream =
                new SequenceInputStream(
                        new FileInputStream(String.format("src/test/resources/xsts/%s", fileName)),
                        new FileInputStream(
                                String.format("src/test/resources/prop/%s", propFileName)))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }
        final Solver abstractionSolver = Z3LegacySolverFactory.getInstance().createSolver();
        final Analysis<XstsState<ExplState>, XstsAction, ExplPrec> analysis =
                XstsAnalysis.create(
                        ExplStmtAnalysis.create(abstractionSolver, xsts.getInitFormula(), 250));
        final LTS<XstsState<ExplState>, XstsAction> lts =
                XstsLts.create(xsts, XstsStmtOptimizer.create(DefaultStmtOptimizer.create()));
        final Predicate<XstsState<ExplState>> statePredicate =
                new XstsStatePredicate<>(new ExplStatePredicate(xsts.getProp(), abstractionSolver));
        final AcceptancePredicate<XstsState<ExplState>, XstsAction> target =
                new AcceptancePredicate<>(statePredicate::test, Unit.INSTANCE);
        final ExplPrec precision = new XstsAllVarsInitPrec().createExpl(xsts);
        var abstractor =
                new LDGAbstractor<>(
                        analysis,
                        lts,
                        target,
                        LoopcheckerSearchStrategy.Companion.getDefault(),
                        new ConsoleLogger(Logger.Level.DETAIL));
        LDG<XstsState<ExplState>, XstsAction> ldg = new LDG<>(target);
        AbstractorResult result = abstractor.check(ldg, precision);
        Assert.assertEquals(isLassoPresent, result.isUnsafe());
    }

    private void testWithCfa() throws IOException {
        final CFA cfa =
                CfaDslManager.createCfa(
                        new FileInputStream(String.format("src/test/resources/cfa/%s", fileName)));
        final CfaLts lts = CfaConfigBuilder.Encoding.SBE.getLts(cfa.getInitLoc());
        final Analysis<CfaState<ExplState>, CfaAction, CfaPrec<ExplPrec>> analysis =
                CfaAnalysis.create(
                        cfa.getInitLoc(),
                        ExplStmtAnalysis.create(
                                Z3LegacySolverFactory.getInstance().createSolver(), True(), 250));
        final CfaPrec<ExplPrec> precision = GlobalCfaPrec.create(ExplPrec.of(cfa.getVars()));
        Predicate<CfaState<ExplState>> statePredicate =
                cfaState -> cfaState.getLoc().getName().equals(acceptingLocationName);
        AcceptancePredicate<CfaState<ExplState>, CfaAction> target =
                new AcceptancePredicate<>(statePredicate::test, Unit.INSTANCE);
        LDGAbstractor<CfaState<ExplState>, CfaAction, CfaPrec<ExplPrec>> abstractor =
                new LDGAbstractor<>(
                        analysis,
                        lts,
                        target,
                        LoopcheckerSearchStrategy.Companion.getDefault(),
                        new ConsoleLogger(Logger.Level.DETAIL));
        LDG<CfaState<ExplState>, CfaAction> ldg = new LDG<>(target);
        AbstractorResult result = abstractor.check(ldg, precision);
        Assert.assertEquals(isLassoPresent, result.isUnsafe());
    }
}
