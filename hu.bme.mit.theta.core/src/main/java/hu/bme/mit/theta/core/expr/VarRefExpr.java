package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public abstract class VarRefExpr<DeclType extends Type> extends RefExpr<DeclType> {

	@Override
	public abstract VarDecl<DeclType> getDecl();

}
