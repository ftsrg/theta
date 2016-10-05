package hu.bme.mit.theta.analysis.cfa;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.automaton.AutomatonAnalysis;
import hu.bme.mit.theta.analysis.automaton.AutomatonPrecision;
import hu.bme.mit.theta.analysis.automaton.AutomatonState;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;

public final class CfaAnalysis<S extends State, P extends Precision>
		implements Analysis<AutomatonState<S, CfaLoc, CfaEdge>, CfaAction, AutomatonPrecision<P, CfaLoc, CfaEdge>> {

	private final AutomatonAnalysis<S, CfaAction, P, CfaLoc, CfaEdge> automatonAnalysis;

	private CfaAnalysis(final CfaLoc initLoc, final Analysis<S, CfaAction, P> analysis) {
		automatonAnalysis = AutomatonAnalysis.create(initLoc, analysis, CfaAction::create);
	}

	public static <S extends State, P extends Precision> CfaAnalysis<S, P> create(final CfaLoc initLoc,
			final Analysis<S, CfaAction, P> analysis) {
		return new CfaAnalysis<>(initLoc, analysis);
	}

	@Override
	public Domain<AutomatonState<S, CfaLoc, CfaEdge>> getDomain() {
		return automatonAnalysis.getDomain();
	}

	@Override
	public InitFunction<AutomatonState<S, CfaLoc, CfaEdge>, AutomatonPrecision<P, CfaLoc, CfaEdge>> getInitFunction() {
		return automatonAnalysis.getInitFunction();
	}

	@Override
	public TransferFunction<AutomatonState<S, CfaLoc, CfaEdge>, CfaAction, AutomatonPrecision<P, CfaLoc, CfaEdge>> getTransferFunction() {
		return automatonAnalysis.getTransferFunction();
	}

	@Override
	public ActionFunction<? super AutomatonState<S, CfaLoc, CfaEdge>, ? extends CfaAction> getActionFunction() {
		return automatonAnalysis.getActionFunction();
	}

}
