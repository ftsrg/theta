package hu.bme.mit.theta.analysis.tcfa;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.automaton.AutomatonAnalysis;
import hu.bme.mit.theta.analysis.automaton.AutomatonState;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaAnalyis<S extends State, P extends Precision>
		implements Analysis<AutomatonState<S, TcfaLoc, TcfaEdge>, TcfaAction, P> {

	private final AutomatonAnalysis<S, TcfaAction, P, TcfaLoc, TcfaEdge> automatonAnalysis;

	private TcfaAnalyis(final TcfaLoc initLoc, final Analysis<S, TcfaAction, P> analysis) {
		automatonAnalysis = AutomatonAnalysis.create(initLoc, analysis, TcfaAction::create);
	}

	public static <S extends State, P extends Precision> TcfaAnalyis<S, P> create(final TcfaLoc initLoc,
			final Analysis<S, TcfaAction, P> analysis) {
		return new TcfaAnalyis<>(initLoc, analysis);
	}

	@Override
	public Domain<AutomatonState<S, TcfaLoc, TcfaEdge>> getDomain() {
		return automatonAnalysis.getDomain();
	}

	@Override
	public InitFunction<AutomatonState<S, TcfaLoc, TcfaEdge>, P> getInitFunction() {
		return automatonAnalysis.getInitFunction();
	}

	@Override
	public TransferFunction<AutomatonState<S, TcfaLoc, TcfaEdge>, TcfaAction, P> getTransferFunction() {
		return automatonAnalysis.getTransferFunction();
	}

	@Override
	public ActionFunction<? super AutomatonState<S, TcfaLoc, TcfaEdge>, ? extends TcfaAction> getActionFunction() {
		return automatonAnalysis.getActionFunction();
	}

}
