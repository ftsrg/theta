package hu.bme.mit.theta.xsts.analysis.maxatomcount;

import hu.bme.mit.theta.analysis.expr.refinement.maxatomcount.MaxAtomCount;
import hu.bme.mit.theta.xsts.XSTS;

public interface XstsMaxAtomCountFactory {

    MaxAtomCount create(final XSTS xsts);

}
