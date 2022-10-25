package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;

public interface XtaRefToPrec <P extends Prec, R extends Refutation> extends RefutationToPrec<Prod2Prec<P, ZonePrec>, R> {
}
