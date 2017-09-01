package hu.bme.mit.theta.formalism.cfa.analysis;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public interface CfaPrec<P extends Prec> extends Prec {
	P getPrec(final Loc loc);
}
