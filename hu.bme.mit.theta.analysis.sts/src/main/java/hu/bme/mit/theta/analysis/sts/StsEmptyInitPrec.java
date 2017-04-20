package hu.bme.mit.theta.analysis.sts;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;

public class StsEmptyInitPrec implements StsInitPrec {

	@Override
	public ExplPrec createExpl(final STS sts) {
		return ExplPrec.create();
	}

	@Override
	public SimplePredPrec createSimplePred(final STS sts, final Solver solver) {
		return SimplePredPrec.create(solver);
	}

}
