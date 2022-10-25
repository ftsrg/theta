package hu.bme.mit.theta.xta.analysis.prec;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.analysis.XtaState;

import java.util.Collection;

public interface XtaPrec <P extends Prec> extends Prec{
    P getPrec(final Collection<XtaProcess.Loc> loc);
}
