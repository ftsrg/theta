package hu.bme.mit.inf.ttmc.constraint.decl;

import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface Decl<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> {
	public String getName();

	public DeclType getType();

	public RefExpr<DeclType, DeclKind> getRef();
}
