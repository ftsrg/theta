package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.impl.NullPrec;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.loc.ConstLocPrec;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrec;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod.Prod2Prec;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.prod.ProdPrec;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.zone.itp.ItpZoneState;
import hu.bme.mit.theta.analysis.tcfa.zone.itp.TcfaItpZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;

final class TcfaLawiAnalysis implements Analysis<TcfaLawiState, TcfaAction, NullPrec> {

	private final Domain<TcfaLawiState> domain;
	private final InitFunction<TcfaLawiState, NullPrec> initFunction;
	private final TransferFunction<TcfaLawiState, TcfaAction, NullPrec> transferFunction;

	private TcfaLawiAnalysis(final TCFA tcfa, final Solver solver) {
		checkNotNull(tcfa);
		checkNotNull(solver);

		final ExplPrec explPrec = ExplPrec.create(tcfa.getDataVars());
		final ZonePrec zonePrec = ZonePrec.create(tcfa.getClockVars());
		final Prod2Prec<ExplPrec, ZonePrec> compositePrec = ProdPrec.of(explPrec, zonePrec);
		final LocPrec<Prod2Prec<ExplPrec, ZonePrec>, TcfaLoc, TcfaEdge> locPrec = ConstLocPrec.create(compositePrec);

		final Analysis<ExplState, ExprAction, ExplPrec> explAnalysis = ExplAnalysis.create(solver, True());
		final Analysis<ItpZoneState, TcfaAction, ZonePrec> itpZoneAnalysis = TcfaItpZoneAnalysis.getInstance();
		final Analysis<Prod2State<ExplState, ItpZoneState>, TcfaAction, Prod2Prec<ExplPrec, ZonePrec>> compositeAnalysis = Prod2Analysis
				.create(explAnalysis, itpZoneAnalysis);
		final Analysis<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrec<Prod2Prec<ExplPrec, ZonePrec>, TcfaLoc, TcfaEdge>> locAnalysis = LocAnalysis
				.create(tcfa.getInitLoc(), compositeAnalysis);

		final Analysis<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, NullPrec> analysis = PrecMappingAnalysis
				.create(locAnalysis, np -> locPrec);

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
	public InitFunction<TcfaLawiState, NullPrec> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<TcfaLawiState, TcfaAction, NullPrec> getTransferFunction() {
		return transferFunction;
	}

}
