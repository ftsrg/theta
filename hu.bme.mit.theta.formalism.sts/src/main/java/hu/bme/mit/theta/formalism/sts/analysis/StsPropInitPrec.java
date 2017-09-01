package hu.bme.mit.theta.formalism.sts.analysis;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;

/**
 * An implementation for initial precision that returns initial precisions based
 * on the property.
 */
public class StsPropInitPrec implements StsInitPrec {

	@Override
	public ExplPrec createExpl(final STS sts) {
		return ExplPrec.create(ExprUtils.getVars(sts.getProp()));
	}

	@Override
	public SimplePredPrec createSimplePred(final STS sts, final Solver solver) {
		return SimplePredPrec.create(ExprUtils.getAtoms(sts.getProp()), solver);
	}

}
