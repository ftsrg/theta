package hu.bme.mit.theta.xsts.type;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface XstsType<T extends Type> {

    T getType();

    Expr<BoolType> createBoundExpr(final VarDecl<T> decl);

    String serializeLiteral(final LitExpr<T> literal);

}
