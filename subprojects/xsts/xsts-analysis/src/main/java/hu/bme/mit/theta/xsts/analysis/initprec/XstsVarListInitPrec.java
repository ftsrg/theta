package hu.bme.mit.theta.xsts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xsts.XSTS;
import jdk.jshell.spi.ExecutionControl;

import java.util.Set;

public class XstsVarListInitPrec implements XstsInitPrec {
    Set<VarDecl<?>> vars;

    public XstsVarListInitPrec(Set<VarDecl<?>> vars) {
        this.vars = vars;
    }

    @Override
    public ExplPrec createExpl(XSTS xsts) {
        return ExplPrec.of(vars);
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
