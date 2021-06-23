package hu.bme.mit.theta.analysis.expr.refinement.autoexpl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface AutoExpl {

    boolean isExpl(final VarDecl<?> decl);

    void update(final Expr<BoolType> itp);

}
