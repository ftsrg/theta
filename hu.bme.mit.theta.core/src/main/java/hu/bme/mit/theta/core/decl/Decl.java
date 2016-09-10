package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

public interface Decl<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> {
	public String getName();

	public DeclType getType();

	public RefExpr<DeclType, DeclKind> getRef();

	public <P, R> R accept(DeclVisitor<? super P, ? extends R> visitor, P param);
}
