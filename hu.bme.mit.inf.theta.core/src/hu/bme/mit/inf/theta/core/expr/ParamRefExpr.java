package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.type.Type;

public interface ParamRefExpr<DeclType extends Type> extends RefExpr<DeclType, ParamDecl<DeclType>> {
}
