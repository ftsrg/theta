package hu.bme.mit.theta.analysis.tcfa.pred;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.pred.PredDomain;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.solver.Solver;

public class TcfaPredAnalysis implements Analysis<PredState, TcfaAction, PredPrecision> {

	private final Domain<PredState> domain;
	private final TransferFunction<PredState, TcfaAction, PredPrecision> transferFunction;

	public TcfaPredAnalysis(final Solver solver) {
		domain = PredDomain.create(solver);
		transferFunction = new TcfaPredTransferFunction(solver);
	}

	@Override
	public Domain<PredState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<PredState, PredPrecision> getInitFunction() {
		return TcfaPredInitFunction.getInstance();
	}

	@Override
	public TransferFunction<PredState, TcfaAction, PredPrecision> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super PredState, ? extends TcfaAction> getActionFunction() {
		throw new UnsupportedOperationException();
	}

}
