package hu.bme.mit.inf.theta.analysis.sts.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.theta.analysis.ActionFunction;
import hu.bme.mit.inf.theta.analysis.Analysis;
import hu.bme.mit.inf.theta.analysis.Domain;
import hu.bme.mit.inf.theta.analysis.InitFunction;
import hu.bme.mit.inf.theta.analysis.TransferFunction;
import hu.bme.mit.inf.theta.analysis.expl.ExplDomain;
import hu.bme.mit.inf.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.theta.analysis.expl.ExplState;
import hu.bme.mit.inf.theta.analysis.sts.StsAction;
import hu.bme.mit.inf.theta.analysis.sts.StsActionFunction;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.solver.Solver;

public class StsExplAnalysis implements Analysis<ExplState, StsAction, ExplPrecision> {

	private final ExplDomain domain;
	private final StsExplInitFunction initFunction;
	private final StsExplTransferFunction transferFunction;
	private final ActionFunction<? super ExplState, ? extends StsAction> actionFunction;

	public StsExplAnalysis(final STS sts, final Solver solver) {
		checkNotNull(sts);
		checkNotNull(solver);
		domain = ExplDomain.getInstance();
		initFunction = new StsExplInitFunction(sts, solver);
		transferFunction = new StsExplTransferFunction(sts, solver);
		actionFunction = new StsActionFunction(sts);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<ExplState, ExplPrecision> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<ExplState, StsAction, ExplPrecision> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super ExplState, ? extends StsAction> getActionFunction() {
		return actionFunction;
	}

}
