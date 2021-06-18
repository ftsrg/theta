package hu.bme.mit.theta.analysis.expr.refinement.maxatomcount;

import hu.bme.mit.theta.core.decl.VarDecl;

public class NMaxAtomCount implements MaxAtomCount{

    private final int n;

    public NMaxAtomCount(final int n){
        this.n=n;
    }

    @Override
    public int get(VarDecl<?> decl) {
        return n;
    }
}
