package hu.bme.mit.inf.ttmc.analysis.sts.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.pred.PredDomain;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.sts.STSAction;
import hu.bme.mit.inf.ttmc.analysis.sts.STSActionFunction;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class STSPredAnalysis implements Analysis<PredState, STSAction, PredPrecision> {

	private final PredDomain domain;
	private final STSPredInitFunction initFunction;
	private final STSPredTransferFunction transferFunction;
	private final ActionFunction<? super PredState, ? extends STSAction> actionFunction;

	public STSPredAnalysis(final STS sts, final Solver solver) {
		checkNotNull(sts);
		checkNotNull(solver);
		domain = PredDomain.create(solver);
		initFunction = new STSPredInitFunction(sts, solver);
		transferFunction = new STSPredTransferFunction(sts, solver);
		actionFunction = new STSActionFunction(sts);
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
	public TransferFunction<PredState, STSAction, PredPrecision> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super PredState, ? extends STSAction> getActionFunction() {
		return actionFunction;
	}

}
