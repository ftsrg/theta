package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;

public interface RefExpr<DeclType extends Type> extends NullaryExpr<DeclType> {

	public Decl<DeclType> getDecl();

}
