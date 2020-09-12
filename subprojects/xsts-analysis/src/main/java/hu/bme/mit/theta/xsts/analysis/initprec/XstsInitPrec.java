package hu.bme.mit.theta.xsts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.xsts.XSTS;

public interface XstsInitPrec {
	/**
	 * Creates initial ExplPrec based on an XSTS.
	 */
	ExplPrec createExpl(XSTS xsts);

	/**
	 * Creates initial PredPrec based on an XSTS.
	 */
	PredPrec createPred(XSTS xsts);

	/**
	 * Creates initial Prod2ExplPredPrec based on an XSTS.
	 */
	Prod2Prec<ExplPrec, PredPrec> createProd2ExplPred(XSTS xsts);
}
