package hu.bme.mit.theta.analysis.prod2.prod2explpred.dynamic;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;

import static com.google.common.base.Preconditions.checkNotNull;

public class ItpRefToDynamicPrec implements RefutationToPrec<DynamicPrec, ItpRefutation> {

    private final ItpRefToExplPrec itpRefToExplPrec;
    private final ItpRefToPredPrec itpRefToPredPrec;

    private ItpRefToDynamicPrec(final ItpRefToExplPrec itpRefToExplPrec, final ItpRefToPredPrec itpRefToPredPrec) {
        this.itpRefToExplPrec = checkNotNull(itpRefToExplPrec);
        this.itpRefToPredPrec = checkNotNull(itpRefToPredPrec);
    }

    public static ItpRefToDynamicPrec create(final ItpRefToExplPrec itpRefToExplPrec, final ItpRefToPredPrec itpRefToPredPrec) {
        return new ItpRefToDynamicPrec(itpRefToExplPrec, itpRefToPredPrec);
    }

    @Override
    public DynamicPrec toPrec(ItpRefutation refutation, int index) {
        final ExplPrec explPrec = itpRefToExplPrec.toPrec(refutation, index);
        final PredPrec predPrec = itpRefToPredPrec.toPrec(refutation, index);
        return DynamicPrec.of(explPrec, predPrec);

    }

    @Override
    public DynamicPrec join(DynamicPrec prec1, DynamicPrec prec2) {
        return DynamicPrec.of(prec1.getPrec1().join(prec2.getPrec1()), prec1.getPrec2().join(prec2.getPrec2()));
    }

    @Override
    public String toString() {
        return getClass().getSimpleName();
    }

}
