package hu.bme.mit.theta.analysis.cfa;

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
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;

public final class CfaAnalysis<S extends State, P extends Precision>
		implements Analysis<LocState<S, CfaLoc, CfaEdge>, CfaAction, LocPrecision<P, CfaLoc, CfaEdge>> {

	private final LocAnalysis<S, CfaAction, P, CfaLoc, CfaEdge> locAnalysis;

	private CfaAnalysis(final CfaLoc initLoc, final Analysis<S, CfaAction, P> analysis) {
		locAnalysis = LocAnalysis.create(initLoc, analysis, CfaAction::create);
	}

	public static <S extends State, P extends Precision> CfaAnalysis<S, P> create(final CfaLoc initLoc,
			final Analysis<S, CfaAction, P> analysis) {
		return new CfaAnalysis<>(initLoc, analysis);
	}

	@Override
	public Domain<LocState<S, CfaLoc, CfaEdge>> getDomain() {
		return locAnalysis.getDomain();
	}

	@Override
	public InitFunction<LocState<S, CfaLoc, CfaEdge>, LocPrecision<P, CfaLoc, CfaEdge>> getInitFunction() {
		return locAnalysis.getInitFunction();
	}

	@Override
	public TransferFunction<LocState<S, CfaLoc, CfaEdge>, CfaAction, LocPrecision<P, CfaLoc, CfaEdge>> getTransferFunction() {
		return locAnalysis.getTransferFunction();
	}

	@Override
	public ActionFunction<? super LocState<S, CfaLoc, CfaEdge>, ? extends CfaAction> getActionFunction() {
		return locAnalysis.getActionFunction();
	}

}
