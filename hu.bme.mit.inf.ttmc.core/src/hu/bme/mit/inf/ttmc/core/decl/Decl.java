package hu.bme.mit.inf.ttmc.core.decl;

import hu.bme.mit.inf.ttmc.core.expr.RefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.DeclVisitor;

public interface Decl<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> {
	public String getName();

	public DeclType getType();

	public RefExpr<DeclType, DeclKind> getRef();

	public <P, R> R accept(DeclVisitor<? super P, ? extends R> visitor, P param);
}
