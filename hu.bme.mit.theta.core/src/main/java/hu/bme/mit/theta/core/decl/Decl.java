package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

public interface Decl<DeclType extends Type> {
	String getName();

	DeclType getType();

	RefExpr<DeclType> getRef();

	<P, R> R accept(DeclVisitor<? super P, ? extends R> visitor, P param);
}
