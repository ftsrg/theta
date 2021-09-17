package hu.bme.mit.theta.xsts.analysis.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.StaticAutoExpl;
import hu.bme.mit.theta.xsts.XSTS;

public class XstsStaticAutoExpl implements XstsAutoExpl{
    @Override
    public AutoExpl create(XSTS xsts) {
        return new StaticAutoExpl(xsts.getCtrlVars());
    }
}
