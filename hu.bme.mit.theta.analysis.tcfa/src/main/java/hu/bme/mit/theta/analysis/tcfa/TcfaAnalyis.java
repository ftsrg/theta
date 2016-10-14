package hu.bme.mit.theta.analysis.tcfa;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaAnalyis<S extends State, P extends Precision>
		implements Analysis<LocState<S, TcfaLoc, TcfaEdge>, TcfaAction, LocPrecision<P, TcfaLoc, TcfaEdge>> {

	private final LocAnalysis<S, TcfaAction, P, TcfaLoc, TcfaEdge> locAnalysis;

	private TcfaAnalyis(final TcfaLoc initLoc, final Analysis<S, TcfaAction, P> analysis) {
		locAnalysis = LocAnalysis.create(initLoc, analysis, TcfaAction::create);
	}

	public static <S extends State, P extends Precision> TcfaAnalyis<S, P> create(final TcfaLoc initLoc,
			final Analysis<S, TcfaAction, P> analysis) {
		return new TcfaAnalyis<>(initLoc, analysis);
	}

	@Override
	public Domain<LocState<S, TcfaLoc, TcfaEdge>> getDomain() {
		return locAnalysis.getDomain();
	}

	@Override
	public InitFunction<LocState<S, TcfaLoc, TcfaEdge>, LocPrecision<P, TcfaLoc, TcfaEdge>> getInitFunction() {
		return locAnalysis.getInitFunction();
	}

	@Override
	public TransferFunction<LocState<S, TcfaLoc, TcfaEdge>, TcfaAction, LocPrecision<P, TcfaLoc, TcfaEdge>> getTransferFunction() {
		return locAnalysis.getTransferFunction();
	}

	@Override
	public ActionFunction<? super LocState<S, TcfaLoc, TcfaEdge>, ? extends TcfaAction> getActionFunction() {
		return locAnalysis.getActionFunction();
	}

}
