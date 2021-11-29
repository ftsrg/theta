package hu.bme.mit.theta.analysis.prod2.prod2explpred.mixed;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;

import static com.google.common.base.Preconditions.checkNotNull;

public class ItpRefToMixedPrec implements RefutationToPrec<Prod2Prec<ExplPrec, PredPrec>, ItpRefutation> {

    private final ItpRefToExplPrec itpRefToExplPrec;
    private final ItpRefToPredPrec itpRefToPredPrec;

    private ItpRefToMixedPrec(final ItpRefToExplPrec itpRefToExplPrec, final ItpRefToPredPrec itpRefToPredPrec) {
        this.itpRefToExplPrec = checkNotNull(itpRefToExplPrec);
        this.itpRefToPredPrec = checkNotNull(itpRefToPredPrec);
    }

    public static ItpRefToMixedPrec create(final ItpRefToExplPrec itpRefToExplPrec, final ItpRefToPredPrec itpRefToPredPrec) {
        return new ItpRefToMixedPrec(itpRefToExplPrec, itpRefToPredPrec);
    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> toPrec(ItpRefutation refutation, int index) {
        final ExplPrec explPrec = itpRefToExplPrec.toPrec(refutation, index);
        final PredPrec predPrec = itpRefToPredPrec.toPrec(refutation, index);
        return Prod2Prec.of(explPrec, predPrec);

    }

    @Override
    public Prod2Prec<ExplPrec, PredPrec> join(Prod2Prec<ExplPrec, PredPrec> prec1, Prod2Prec<ExplPrec, PredPrec> prec2) {
        return Prod2Prec.of(prec1.getPrec1().join(prec2.getPrec1()), prec1.getPrec2().join(prec2.getPrec2()));
    }

    @Override
    public String toString() {
        return getClass().getSimpleName();
    }

}
