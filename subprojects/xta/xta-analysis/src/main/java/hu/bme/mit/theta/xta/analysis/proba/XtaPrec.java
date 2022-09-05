package hu.bme.mit.theta.xta.analysis.proba;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.xta.XtaProcess;

public interface XtaPrec <P extends Prec> extends Prec{
    P getPrec(final XtaProcess.Loc loc);
}
