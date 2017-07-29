package hu.bme.mit.theta.analysis.xta;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.unit.UnitAnalysis;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.unit.UnitState;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.common.Tuple;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.dsl.XtaDslManager;

@RunWith(Parameterized.class)
public final class XtaAnalysisTest {

	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "/critical-2-25-50.xta" },

				{ "/csma-2.xta" },

				{ "/fddi-2.xta" },

				{ "/fischer-2-32-64.xta" },

				{ "/lynch-2-16.xta" }

		});
	}

	@Parameter(0)
	public String filepath;

	@Test
	public void test() throws FileNotFoundException, IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		final XtaSystem system = XtaDslManager.createSystem(inputStream);

		final LTS<XtaState<?>, XtaAction> lts = XtaLts.create();
		final Analysis<XtaState<UnitState>, XtaAction, UnitPrec> analysis = XtaAnalysis.create(system,
				UnitAnalysis.getInstance());
		final ArgBuilder<XtaState<UnitState>, XtaAction, UnitPrec> argBuilder = ArgBuilder.create(lts, analysis,
				s -> false);

		final Abstractor<XtaState<UnitState>, XtaAction, UnitPrec> abstractor = WaitlistBasedAbstractor
				.create(argBuilder, s -> Tuple.of(s.getLocs(), s.getVal()), FifoWaitlist.supplier());

		final ARG<XtaState<UnitState>, XtaAction> arg = abstractor.createArg();
		abstractor.check(arg, UnitPrec.getInstance());

		System.out.println(GraphvizWriter.getInstance().writeString(ArgVisualizer.visualize(arg)));
	}

}
