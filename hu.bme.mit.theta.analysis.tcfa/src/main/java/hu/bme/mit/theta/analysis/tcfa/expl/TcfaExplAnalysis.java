package hu.bme.mit.theta.analysis.tcfa.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplDomain;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.solver.Solver;

public final class TcfaExplAnalysis implements Analysis<ExplState, TcfaAction, ExplPrecision> {

	private final TcfaExplTransferFunction transferFunction;

	private TcfaExplAnalysis(final Solver solver) {
		checkNotNull(solver);
		transferFunction = TcfaExplTransferFunction.create(solver);
	}

	public static TcfaExplAnalysis create(final Solver solver) {
		return new TcfaExplAnalysis(solver);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return ExplDomain.getInstance();
	}

	@Override
	public InitFunction<ExplState, ExplPrecision> getInitFunction() {
		return TcfaExplInitFunction.getInstance();
	}

	@Override
	public TransferFunction<ExplState, TcfaAction, ExplPrecision> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super ExplState, ? extends TcfaAction> getActionFunction() {
		throw new UnsupportedOperationException();
	}

}
