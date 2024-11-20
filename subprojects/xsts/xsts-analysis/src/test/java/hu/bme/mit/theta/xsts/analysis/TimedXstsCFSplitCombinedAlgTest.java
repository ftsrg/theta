package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfig;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;
import hu.bme.mit.theta.xsts.analysis.config.TimedXstsConfigBuilder;
import hu.bme.mit.theta.xsts.dsl.XstsDslManager;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.*;
import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.assertTrue;

@RunWith(value = Parameterized.class)
public class TimedXstsCFSplitCombinedAlgTest {

    @Parameterized.Parameter(value = 0)
    public String filePath;

    @Parameterized.Parameter(value = 1)
    public String propPath;

    @Parameterized.Parameter(value = 2)
    public boolean safe;

    @Parameterized.Parameter(value = 3)
    public XstsConfigBuilder.Domain domain;

    @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][] {

                { "src/test/resources/model/Crossroad-Theta_timed.xsts", "src/test/resources/property/crossroad_safety.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/Crossroad-Theta_timed.xsts", "src/test/resources/property/crossroad_safety.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival1.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival1.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival2.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival2.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival3.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival3.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival4.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival4.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival5.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival5.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival6.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival6.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival7.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival7.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival8.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival8.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival9.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival9.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival10.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/ANTIVAL_CHK_COID_System_timed.xsts", "src/test/resources/property/antival10.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/clocks.xsts", "src/test/resources/property/clocks.prop", false, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/clocks.xsts", "src/test/resources/property/clocks.prop", false, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

                { "src/test/resources/model/xta_to_txsts.xsts", "src/test/resources/property/xta_to_txsts.prop", true, XstsConfigBuilder.Domain.EXPL},

                { "src/test/resources/model/xta_to_txsts.xsts", "src/test/resources/property/xta_to_txsts.prop", true, XstsConfigBuilder.Domain.PRED_CART},

                { "src/test/resources/model/xta_to_txsts.xsts", "src/test/resources/property/xta_to_txsts.prop", true, XstsConfigBuilder.Domain.EXPL_PRED_COMBINED},

        });
    }

    @Test
    public void test() throws IOException {

        final Logger logger = new ConsoleLogger(Level.SUBSTEP);

        XSTS xsts;
        try (InputStream inputStream = new SequenceInputStream(new FileInputStream(filePath), new FileInputStream(propPath))) {
            xsts = XstsDslManager.createXsts(inputStream);
        }
        final XstsConfigBuilder xstsConfigBuilder = new XstsConfigBuilder(domain, XstsConfigBuilder.Refinement.SEQ_ITP, Z3SolverFactory.getInstance())
                .initPrec(XstsConfigBuilder.InitPrec.CTRL)
                .optimizeStmts(XstsConfigBuilder.OptimizeStmts.ON)
                .predSplit(XstsConfigBuilder.PredSplit.CONJUNCTS)
                .maxEnum(250)
                .pruneStrategy(PruneStrategy.FULL)
                .clockReplacer(XstsConfigBuilder.ClockReplacer.NONE)
                .logger(logger);
        final XstsConfig<?, ?, ?> configuration = new TimedXstsConfigBuilder(xstsConfigBuilder)
                .controlFlowSplitting(TimedXstsConfigBuilder.ControlFlowSplitting.FEASIBLE_ACTIONS_ONLY)
                .build(xsts);
        final SafetyResult<?, ?> status = configuration.check();
        if (safe) {
            assertTrue(status.isSafe());
        } else {
            assertTrue(status.isUnsafe());
        }
    }

}
