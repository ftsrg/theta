package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
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
import hu.bme.mit.theta.analysis.tcfa.expl.TcfaExplAnalysis;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaZoneAnalysis;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

final class TcfaLawiAnalysis implements Analysis<TcfaLawiState, TcfaAction, UnitPrec> {

	private final Domain<TcfaLawiState> domain;
	private final InitFunction<TcfaLawiState, UnitPrec> initFunction;
	private final TransferFunction<TcfaLawiState, TcfaAction, UnitPrec> transferFunction;

	private TcfaLawiAnalysis(final TCFA tcfa) {
		checkNotNull(tcfa);

		final ExplPrec explPrec = ExplPrec.create(tcfa.getDataVars());
		final ZonePrec zonePrec = ZonePrec.of(tcfa.getClockVars());
		final Prod2Prec<ExplPrec, ZonePrec> compositePrec = ProdPrec.of(explPrec, zonePrec);
		final LocPrec<Prod2Prec<ExplPrec, ZonePrec>, TcfaLoc, TcfaEdge> locPrec = ConstLocPrec.create(compositePrec);

		final Analysis<ExplState, TcfaAction, ExplPrec> explAnalysis = TcfaExplAnalysis.getInstance();
		final Analysis<ItpZoneState, TcfaAction, ZonePrec> itpZoneAnalysis = ItpZoneAnalysis
				.create(TcfaZoneAnalysis.getInstance());
		final Analysis<Prod2State<ExplState, ItpZoneState>, TcfaAction, Prod2Prec<ExplPrec, ZonePrec>> compositeAnalysis = Prod2Analysis
				.create(explAnalysis, itpZoneAnalysis);
		final Analysis<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, LocPrec<Prod2Prec<ExplPrec, ZonePrec>, TcfaLoc, TcfaEdge>> locAnalysis = LocAnalysis
				.create(tcfa.getInitLoc(), compositeAnalysis);

		final Analysis<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction, UnitPrec> analysis = PrecMappingAnalysis
				.create(locAnalysis, np -> locPrec);

		domain = TcfaLawiDomain.create(analysis.getDomain());
		initFunction = TcfaLawiInitFunction.create(analysis.getInitFunction());
		transferFunction = TcfaLawiTransferFunction.create(analysis.getTransferFunction());
	}

	public static TcfaLawiAnalysis create(final TCFA tcfa) {
		return new TcfaLawiAnalysis(tcfa);
	}

	@Override
	public Domain<TcfaLawiState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<TcfaLawiState, UnitPrec> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<TcfaLawiState, TcfaAction, UnitPrec> getTransferFunction() {
		return transferFunction;
	}

}
