package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;

public abstract class RefExpr<DeclType extends Type> extends NullaryExpr<DeclType> {

	public abstract Decl<DeclType> getDecl();

}
