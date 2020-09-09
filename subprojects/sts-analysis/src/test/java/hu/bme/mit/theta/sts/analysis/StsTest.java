package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.Utils;
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

import static hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.Domain.*;
import static hu.bme.mit.theta.sts.analysis.config.StsConfigBuilder.Refinement.SEQ_ITP;

@RunWith(value = Parameterized.class)
public class StsTest {
	@Parameterized.Parameter(value = 0)
	public String filePath;

	@Parameterized.Parameter(value = 1)
	public StsConfigBuilder.Domain domain;

	@Parameterized.Parameter(value = 2)
	public StsConfigBuilder.Refinement refinement;

	@Parameterized.Parameter(value = 3)
	public boolean isSafe;

	@Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{
				{ "src/test/resources/hw1_false.aag", PRED_CART, SEQ_ITP, false },
				
				{ "src/test/resources/hw2_true.aag", PRED_CART, SEQ_ITP, true },

				{ "src/test/resources/boolean1.system", PRED_CART, SEQ_ITP, false },

				{ "src/test/resources/boolean2.system", PRED_CART, SEQ_ITP, false },

				{ "src/test/resources/counter.system", PRED_CART, SEQ_ITP, true },

				{ "src/test/resources/counter_bad.system", PRED_CART, SEQ_ITP, false },

				{ "src/test/resources/counter_parametric.system", PRED_CART, SEQ_ITP, true },

				{ "src/test/resources/loop.system", EXPL, SEQ_ITP, true },

				{ "src/test/resources/loop_bad.system", EXPL, SEQ_ITP, false },

				{ "src/test/resources/multipleinitial.system", PRED_CART, SEQ_ITP, false },

				{ "src/test/resources/readerswriters.system", PRED_CART, SEQ_ITP, true },

				{ "src/test/resources/simple1.system", EXPL, SEQ_ITP, false },

				{ "src/test/resources/simple2.system", EXPL, SEQ_ITP, true },

				{ "src/test/resources/simple3.system", EXPL, SEQ_ITP, false },
		});
	}

	@Test
	public void test() throws IOException {
		STS sts = null;
		if (filePath.endsWith("aag")) sts = AigerToSts.createSts(AigerParser.parse(filePath));
		else {
			final StsSpec spec = StsDslManager.createStsSpec(new FileInputStream(filePath));
			if (spec.getAllSts().size() != 1)
				throw new UnsupportedOperationException("STS contains multiple properties.");
			sts = Utils.singleElementOf(spec.getAllSts());
		}
		StsConfig<? extends State, ? extends Action, ? extends Prec> config
				= new StsConfigBuilder(domain, refinement, Z3SolverFactory.getInstance()).build(sts);
		Assert.assertEquals(isSafe, config.check().isSafe());
	}

}
