package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Type;

public interface ConstRefExpr<DeclType extends Type> extends RefExpr<DeclType> {

	@Override
	public ConstDecl<DeclType> getDecl();

}
