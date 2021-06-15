package hu.bme.mit.theta.analysis.expr.refinement.maxatomcount;

import hu.bme.mit.theta.core.decl.VarDecl;

public class UnlimitedMaxAtomCount implements MaxAtomCount {

    @Override
    public int get(VarDecl<?> decl) {
        return 0;
    }

}
