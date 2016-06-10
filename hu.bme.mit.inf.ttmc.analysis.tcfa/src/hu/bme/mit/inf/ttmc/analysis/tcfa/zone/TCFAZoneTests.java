package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.ttmc.analysis.algorithm.NullLabeling;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAnalysisContext;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFADomain;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAInitFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFALocTargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATransferFunction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneDomain;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.instances.FischerTCFA;

public class TCFAZoneTests {

	@Test
	public void test() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final FischerTCFA fischer = new FischerTCFA(1, 1, 2, vlock);

		final TCFAAnalysisContext context = new TCFAAnalysisContext(fischer.getInitial(), fischer.getCritical());

		final TCFADomain<ZoneState> domain = new TCFADomain<>(ZoneDomain.getInstance());
		final TCFAInitFunction<ZoneState, ZonePrecision> initFunction = new TCFAInitFunction<>(
				new TCFAZoneInitFunction());
		final TCFATransferFunction<ZoneState, ZonePrecision> transferFunction = new TCFATransferFunction<>(
				new TCFAZoneTransferFunction());
		final TCFALocTargetPredicate targetPredicate = new TCFALocTargetPredicate();

		final ZonePrecision precision = ZonePrecision.builder().add(fischer.getClock()).build();

		final Abstractor<TCFAState<ZoneState>, ZonePrecision, Void, Void, TCFALoc, TCFATrans, TCFALoc> abstractor = new Abstractor<>(
				context, NullLabeling.getInstance(), domain, initFunction, transferFunction, targetPredicate);

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));

	}

}
