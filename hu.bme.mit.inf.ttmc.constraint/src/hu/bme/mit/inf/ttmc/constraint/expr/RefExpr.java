package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface RefExpr<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>>
		extends NullaryExpr<DeclType> {
	public DeclKind getDecl();
}
