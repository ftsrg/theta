package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Type;

public abstract class ConstRefExpr<DeclType extends Type> extends RefExpr<DeclType> {

	@Override
	public abstract ConstDecl<DeclType> getDecl();

}
