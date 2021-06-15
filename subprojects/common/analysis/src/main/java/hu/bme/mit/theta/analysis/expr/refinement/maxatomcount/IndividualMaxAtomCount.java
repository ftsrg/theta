package hu.bme.mit.theta.analysis.expr.refinement.maxatomcount;

import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.Map;

public class IndividualMaxAtomCount implements MaxAtomCount{
    private Map<VarDecl<?>,Integer> declToCount;

    public IndividualMaxAtomCount(final Map<VarDecl<?>,Integer> declToCount){
        this.declToCount = declToCount;
    }

    @Override
    public int get(VarDecl<?> decl) {
        return declToCount.get(decl);
    }
}
