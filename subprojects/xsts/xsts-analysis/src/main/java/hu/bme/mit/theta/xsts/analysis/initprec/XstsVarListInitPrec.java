package hu.bme.mit.theta.xsts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.xsts.XSTS;
import jdk.jshell.spi.ExecutionControl;

public class XstsVarListInitPrec implements XstsInitPrec {
    @Override
    public ExplPrec createExpl(XSTS xsts) {
        return null;
    }

    @Override
    public PredPrec createPred(XSTS xsts) {
        throw new RuntimeException("Predicate precision is not supported with variable list precision");
    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> createProd2ExplPred(XSTS xsts) {
        throw new RuntimeException("Prod2ExplPred precision is not supported with variable list precision");
    }
}
