package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.HashSet;
import java.util.Set;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class ItpRefToProd2ExplPredPrec implements RefutationToPrec<Prod2Prec<ExplPrec, PredPrec>, ItpRefutation> {

    private final Set<VarDecl> explPreferredVars;

    private ItpRefToProd2ExplPredPrec(final Set<VarDecl> explPreferredVars){
        this.explPreferredVars=explPreferredVars;
    }

    public static ItpRefToProd2ExplPredPrec create(final Set<VarDecl> explPreferredVars){
        return new ItpRefToProd2ExplPredPrec(explPreferredVars);
    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> toPrec(ItpRefutation refutation, int index) {
        Set<VarDecl<?>> containedVars = ExprUtils.getVars(refutation.get(index));
        Set<VarDecl<?>> explSelectedVars = new HashSet<>();
        boolean allExpl = true;
        for(VarDecl<?> decl:containedVars){
            if(explPreferredVars.contains(decl)){
                explSelectedVars.add(decl);
            } else allExpl = false;
        }
        if(allExpl){
            return Prod2Prec.of(ExplPrec.of(explSelectedVars),PredPrec.of(True()));
        } else {
            return Prod2Prec.of(ExplPrec.of(explSelectedVars),PredPrec.of(refutation.get(index)));
        }
    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> join(Prod2Prec<ExplPrec, PredPrec> prec1, Prod2Prec<ExplPrec, PredPrec> prec2) {
        return Prod2Prec.of(prec1.getPrec1().join(prec2.getPrec1()),prec1.getPrec2().join(prec2.getPrec2()));
    }

    @Override
    public String toString() {
        return getClass().getSimpleName();
    }
}
