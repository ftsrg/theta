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
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.analysis.xta.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.Tuple;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.dsl.XtaDslManager;

@RunWith(Parameterized.class)
public final class XtaZoneAnalysisTest {

	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				// { "/critical-2-25-50.xta" },

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
		final Analysis<XtaState<ZoneState>, XtaAction, ZonePrec> analysis = XtaAnalysis.create(system,
				XtaZoneAnalysis.getInstance());
		final ZonePrec prec = ZonePrec.of(system.getClockVars());

		final ArgBuilder<XtaState<ZoneState>, XtaAction, ZonePrec> argBuilder = ArgBuilder.create(lts, analysis,
				s -> false);

		final Abstractor<XtaState<ZoneState>, XtaAction, ZonePrec> abstractor = WaitlistBasedAbstractor
				.create(argBuilder, s -> Tuple.of(s.getLocs(), s.getVal()), FifoWaitlist.supplier());

		final ARG<XtaState<ZoneState>, XtaAction> arg = abstractor.createArg();
		abstractor.check(arg, prec);

		System.out.println(arg.getNodes().count());
	}

}
