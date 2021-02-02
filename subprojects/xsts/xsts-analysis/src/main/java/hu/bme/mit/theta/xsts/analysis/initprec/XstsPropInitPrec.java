package hu.bme.mit.theta.xsts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;

public class XstsPropInitPrec implements XstsInitPrec {
	@Override
	public ExplPrec createExpl(XSTS xsts) {
		return ExplPrec.of(ExprUtils.getVars(xsts.getProp()));
	}

	@Override
	public PredPrec createPred(XSTS xsts) {
		return PredPrec.of(ExprUtils.getAtoms(xsts.getProp()));
	}

	@Override
	public Prod2Prec<ExplPrec, PredPrec> createProd2ExplPred(XSTS xsts) {
		return Prod2Prec.of(ExplPrec.of(xsts.getCtrlVars()), PredPrec.of(ExprUtils.getAtoms(xsts.getProp())));
	}
}
