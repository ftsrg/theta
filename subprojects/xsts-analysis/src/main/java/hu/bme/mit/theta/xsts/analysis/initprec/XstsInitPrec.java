package hu.bme.mit.theta.xsts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.xsts.XSTS;

public interface XstsInitPrec {
    /**
     * Creates initial ExplPrec based on an XSTS.
     */
    ExplPrec createExpl(XSTS sts);

    /**
     * Creates initial PredPrec based on an XSTS.
     */
    PredPrec createPred(XSTS sts);
}
