package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.type.Type;

public interface ConstRefExpr<DeclType extends Type> extends RefExpr<DeclType, ConstDecl<DeclType>> {
}
