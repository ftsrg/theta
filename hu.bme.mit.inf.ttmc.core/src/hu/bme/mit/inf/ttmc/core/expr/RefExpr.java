package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface RefExpr<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>>
		extends NullaryExpr<DeclType> {

	public DeclKind getDecl();

}
