package hu.bme.mit.inf.ttmc.analysis.tcfa.composite;

import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;

import java.util.Collections;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.ttmc.analysis.algorithm.NullLabeling;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeDomain;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeInitFunction;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositePrecision;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeState;
import hu.bme.mit.inf.ttmc.analysis.composite.CompositeTransferFunction;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplDomain;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAnalysisContext;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFADomain;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAInitFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATrans;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFATransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.expl.TCFAExplInitFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.expl.TCFAExplTransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.zone.TCFAZoneInitFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.zone.TCFAZoneTransferFunction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneDomain;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.instances.FischerTCFA;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

public class TCFACompositeTests {

	@Test
	public void testExplicit() {
		final VarDecl<IntType> vlock = Var("lock", Int());
		final FischerTCFA fischer = new FischerTCFA(1, 1, 2, vlock);

		final TCFAAnalysisContext context = new TCFAAnalysisContext(fischer.getInitial(), fischer.getCritical());

		final SolverManager manager = new Z3SolverManager();
		final Solver solver = manager.createSolver(true, true);

		final TCFADomain<CompositeState<ZoneState, ExplState>> domain = new TCFADomain<>(
				new CompositeDomain<>(ZoneDomain.getInstance(), ExplDomain.getInstance()));

		final TCFAInitFunction<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> initFunction = new TCFAInitFunction<>(
				new CompositeInitFunction<>(new TCFAZoneInitFunction(), new TCFAExplInitFunction()));

		final TCFATransferFunction<CompositeState<ZoneState, ExplState>, CompositePrecision<ZonePrecision, ExplPrecision>> transferFunction = new TCFATransferFunction<>(
				new CompositeTransferFunction<>(new TCFAZoneTransferFunction(), new TCFAExplTransferFunction(solver)));

		final TCFATargetPredicate targetPredicate = new TCFATargetPredicate();

		final CompositePrecision<ZonePrecision, ExplPrecision> precision = CompositePrecision.create(
				ZonePrecision.builder().add(fischer.getClock()).build(),
				GlobalExplPrecision.create(Collections.singleton(vlock), Collections.emptySet()));

		final Abstractor<TCFAState<CompositeState<ZoneState, ExplState>>, CompositePrecision<ZonePrecision, ExplPrecision>, Void, Void, TCFALoc, TCFATrans, TCFALoc> abstractor = new Abstractor<>(
				context, NullLabeling.getInstance(), domain, initFunction, transferFunction, targetPredicate);

		abstractor.init(precision);
		abstractor.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
	}

}
