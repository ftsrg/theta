package hu.bme.mit.theta.xsts.analysis.maxatomcount;

import hu.bme.mit.theta.analysis.expr.refinement.maxatomcount.UnlimitedMaxAtomCount;
import hu.bme.mit.theta.analysis.expr.refinement.maxatomcount.MaxAtomCount;
import hu.bme.mit.theta.xsts.XSTS;

public class XstsUnlimitedMaxAtomCountFactory implements XstsMaxAtomCountFactory{
    @Override
    public MaxAtomCount create(XSTS xsts) {
        return new UnlimitedMaxAtomCount();
    }
}
