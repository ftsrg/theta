package hu.bme.mit.theta.xsts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.xsts.XSTS;

public class XstsEmptyInitPrec implements XstsInitPrec {

	@Override
	public ExplPrec createExpl(final XSTS sts) {
		return ExplPrec.empty();
	}

	@Override
	public PredPrec createPred(final XSTS sts) {
		return PredPrec.of();
	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> createProd2ExplPred(final XSTS sts) {
		return Prod2Prec.of(ExplPrec.empty(), PredPrec.of());
	}

}
