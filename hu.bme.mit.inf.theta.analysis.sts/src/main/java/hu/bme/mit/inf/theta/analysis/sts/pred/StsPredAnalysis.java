package hu.bme.mit.inf.theta.analysis.sts.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.theta.analysis.ActionFunction;
import hu.bme.mit.inf.theta.analysis.Analysis;
import hu.bme.mit.inf.theta.analysis.Domain;
import hu.bme.mit.inf.theta.analysis.InitFunction;
import hu.bme.mit.inf.theta.analysis.TransferFunction;
import hu.bme.mit.inf.theta.analysis.pred.PredDomain;
import hu.bme.mit.inf.theta.analysis.pred.PredPrecision;
import hu.bme.mit.inf.theta.analysis.pred.PredState;
import hu.bme.mit.inf.theta.analysis.sts.StsAction;
import hu.bme.mit.inf.theta.analysis.sts.StsActionFunction;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.solver.Solver;

public class StsPredAnalysis implements Analysis<PredState, StsAction, PredPrecision> {

	private final PredDomain domain;
	private final StsPredInitFunction initFunction;
	private final StsPredTransferFunction transferFunction;
	private final ActionFunction<? super PredState, ? extends StsAction> actionFunction;

	public StsPredAnalysis(final STS sts, final Solver solver) {
		checkNotNull(sts);
		checkNotNull(solver);
		domain = PredDomain.create(solver);
		initFunction = new StsPredInitFunction(sts, solver);
		transferFunction = new StsPredTransferFunction(sts, solver);
		actionFunction = new StsActionFunction(sts);
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

	@Override
	public ActionFunction<? super PredState, ? extends StsAction> getActionFunction() {
		return actionFunction;
	}

}
