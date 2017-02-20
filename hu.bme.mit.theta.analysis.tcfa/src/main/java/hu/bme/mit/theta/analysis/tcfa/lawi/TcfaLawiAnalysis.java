package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.FixedPrecisionAnalysis;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.ConstLocPrecision;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod.Prod2Precision;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.prod.ProdPrecision;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.zone.itp.ItpZoneState;
import hu.bme.mit.theta.analysis.tcfa.zone.itp.TcfaItpZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;

final class TcfaLawiAnalysis implements Analysis<TcfaLawiState, TcfaAction, NullPrecision> {

	private final Domain<TcfaLawiState> domain;
	private final InitFunction<TcfaLawiState, NullPrecision> initFunction;
	private final TransferFunction<TcfaLawiState, TcfaAction, NullPrecision> transferFunction;

	private TcfaLawiAnalysis(final TCFA tcfa, final Solver solver) {
		checkNotNull(tcfa);
		checkNotNull(solver);

		final ExplPrecision explPrecision = ExplPrecision.create(tcfa.getDataVars());
		final ZonePrecision zonePrecision = ZonePrecision.create(tcfa.getClockVars());
		final Prod2Precision<ExplPrecision, ZonePrecision> compositePrecision = ProdPrecision.of(explPrecision,
				zonePrecision);
		final LocPrecision<Prod2Precision<ExplPrecision, ZonePrecision>, TcfaLoc, TcfaEdge> locPrecision = ConstLocPrecision
				.create(compositePrecision);

		final Analysis<ExplState, ExprAction, ExplPrecision> explAnalysis = ExplAnalysis.create(solver, True());
		final Analysis<ItpZoneState, TcfaAction, ZonePrecision> itpZoneAnalysis = TcfaItpZoneAnalysis.getInstance();
		final Analysis<Prod2State<ExplState, ItpZoneState>, TcfaAction, Prod2Precision<ExplPrecision, ZonePrecision>> compositeAnalysis = Prod2Analysis
				.create(explAnalysis, itpZoneAnalysis);
		final Analysis<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrecision<Prod2Precision<ExplPrecision, ZonePrecision>, TcfaLoc, TcfaEdge>> locAnalysis = LocAnalysis
				.create(tcfa.getInitLoc(), compositeAnalysis);

		final Analysis<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrecision> analysis = FixedPrecisionAnalysis
				.create(locAnalysis, locPrecision);

		domain = TcfaLawiDomain.create(analysis.getDomain());
		initFunction = TcfaLawiInitFunction.create(analysis.getInitFunction());
		transferFunction = TcfaLawiTransferFunction.create(analysis.getTransferFunction());
	}

	public static TcfaLawiAnalysis create(final TCFA tcfa, final Solver solver) {
		return new TcfaLawiAnalysis(tcfa, solver);
	}

	@Override
	public Domain<TcfaLawiState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<TcfaLawiState, NullPrecision> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<TcfaLawiState, TcfaAction, NullPrecision> getTransferFunction() {
		return transferFunction;
	}

}
