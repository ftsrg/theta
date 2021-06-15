package hu.bme.mit.theta.analysis.expr.refinement.maxatomcount;

import hu.bme.mit.theta.core.decl.VarDecl;

public interface MaxAtomCount {

    int get(final VarDecl<?> decl);

}
