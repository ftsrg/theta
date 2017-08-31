package hu.bme.mit.theta.analysis.loc;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;

public interface LocPrec<P extends Prec> extends Prec {

	P getPrec(final CfaLoc loc);
}
