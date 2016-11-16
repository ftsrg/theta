package hu.bme.mit.theta.analysis.sts.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.pred.PredDomain;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.sts.StsAction;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;

public class StsPredAnalysis implements Analysis<PredState, StsAction, PredPrecision> {

	private final PredDomain domain;
	private final StsPredInitFunction initFunction;
	private final StsPredTransferFunction transferFunction;

	public StsPredAnalysis(final STS sts, final Solver solver) {
		checkNotNull(sts);
		checkNotNull(solver);
		domain = PredDomain.create(solver);
		initFunction = new StsPredInitFunction(sts, solver);
		transferFunction = new StsPredTransferFunction(sts, solver);
	}

	@Override
	public Domain<PredState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<PredState, PredPrecision> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<PredState, StsAction, PredPrecision> getTransferFunction() {
		return transferFunction;
	}

}
