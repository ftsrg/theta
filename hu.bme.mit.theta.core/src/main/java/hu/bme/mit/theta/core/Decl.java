package hu.bme.mit.theta.core;

import hu.bme.mit.theta.core.type.anytype.RefExpr;

public interface Decl<DeclType extends Type> {

	String getName();

	DeclType getType();

	RefExpr<DeclType> getRef();

}
