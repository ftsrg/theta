package hu.bme.mit.inf.theta.analysis.tcfa.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.theta.analysis.ActionFunction;
import hu.bme.mit.inf.theta.analysis.Analysis;
import hu.bme.mit.inf.theta.analysis.Domain;
import hu.bme.mit.inf.theta.analysis.InitFunction;
import hu.bme.mit.inf.theta.analysis.TransferFunction;
import hu.bme.mit.inf.theta.analysis.expl.ExplDomain;
import hu.bme.mit.inf.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.theta.analysis.expl.ExplState;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.theta.solver.Solver;

public class TcfaExplAnalysis implements Analysis<ExplState, TcfaAction, ExplPrecision> {

	private final TcfaExplTransferFunction transferFunction;

	public TcfaExplAnalysis(final Solver solver) {
		checkNotNull(solver);
		transferFunction = new TcfaExplTransferFunction(solver);
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
