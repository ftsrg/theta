package hu.bme.mit.theta.analysis.expr.refinement;

import hu.bme.mit.theta.analysis.Prec;

public interface RefutationToPrec<P extends Prec, R extends Refutation> {

	P toPrec(R refutation, int index);

	P join(P prec1, P prec2);
}
