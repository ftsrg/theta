package hu.bme.mit.theta.analysis.sts.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplDomain;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.sts.StsAction;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;

public class StsExplAnalysis implements Analysis<ExplState, StsAction, ExplPrecision> {

	private final ExplDomain domain;
	private final StsExplInitFunction initFunction;
	private final StsExplTransferFunction transferFunction;

	public StsExplAnalysis(final STS sts, final Solver solver) {
		checkNotNull(sts);
		checkNotNull(solver);
		domain = ExplDomain.getInstance();
		initFunction = new StsExplInitFunction(sts, solver);
		transferFunction = new StsExplTransferFunction(sts, solver);
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

}
