package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;

import java.util.HashMap;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaAnalyis;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TcfaState;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.instances.FischerTCFA;

public class TcfaZoneTests {

	@Test
	public void test() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final FischerTCFA fischer = new FischerTCFA(1, 1, 2, vlock);

		final TcfaAnalyis<ZoneState, ZonePrecision> analyis = new TcfaAnalyis<>(fischer.getInitial(),
				TcfaZoneAnalysis.getInstance());

		final HashMap<ClockDecl, Integer> ceilings = new HashMap<>();
		ceilings.put(fischer.getClock(), 2);

		final ZonePrecision precision = new ZonePrecision(ceilings);

		final Abstractor<TcfaState<ZoneState>, TcfaAction, ZonePrecision> abstractor = new AbstractorImpl<>(analyis,
				s -> s.getLoc().equals(fischer.getCritical()));

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));

	}

}
