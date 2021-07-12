package hu.bme.mit.theta.xsts.analysis.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.xsts.XSTS;

public interface XstsAutoExpl {

    AutoExpl create(final XSTS xsts);

}
