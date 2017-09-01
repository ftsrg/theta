package hu.bme.mit.theta.formalism.sts.analysis;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;

/**
 * Common interface for inferring initial precision for STSs.
 */
public interface StsInitPrec {
	/**
	 * Creates initial ExplPrec based on an STS.
	 */
	ExplPrec createExpl(STS sts);

	/**
	 * Creates initial SimplePredPrec based on an STS.
	 */
	SimplePredPrec createSimplePred(STS sts, Solver solver);
}
