package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;

public interface RefExpr<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>>
		extends NullaryExpr<DeclType> {

	public DeclKind getDecl();

}
