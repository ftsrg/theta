package hu.bme.mit.theta.analysis.sts;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;

public interface StsInitPrec {
	ExplPrec createExpl(STS sts);

	SimplePredPrec createSimplePred(STS sts, Solver solver);
}
