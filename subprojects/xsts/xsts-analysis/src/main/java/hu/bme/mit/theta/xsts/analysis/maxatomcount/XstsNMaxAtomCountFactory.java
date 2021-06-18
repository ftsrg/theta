package hu.bme.mit.theta.xsts.analysis.maxatomcount;

import hu.bme.mit.theta.analysis.expr.refinement.maxatomcount.MaxAtomCount;
import hu.bme.mit.theta.analysis.expr.refinement.maxatomcount.NMaxAtomCount;
import hu.bme.mit.theta.xsts.XSTS;

import static com.google.common.base.Preconditions.checkArgument;

public class XstsNMaxAtomCountFactory implements XstsMaxAtomCountFactory{

    private final int n;

    public XstsNMaxAtomCountFactory(final int n){
        checkArgument(n >= 0, "maxatomcount must be greater than 0");
        this.n = n;
    }

    @Override
    public MaxAtomCount create(XSTS xsts) {
        return new NMaxAtomCount(n);
    }
}
