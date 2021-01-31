package hu.bme.mit.theta.xsts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.xsts.XSTS;

public class XstsAllVarsInitPrec implements XstsInitPrec {
	@Override
	public ExplPrec createExpl(XSTS xsts) {
		return ExplPrec.of(xsts.getVars());
	}

	@Override
	public PredPrec createPred(XSTS xsts) {
		return PredPrec.of();
	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> createProd2ExplPred(XSTS xsts) {
		return Prod2Prec.of(ExplPrec.of(xsts.getVars()), PredPrec.of());
	}
}
