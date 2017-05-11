package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Type;

public abstract class ParamRefExpr<DeclType extends Type> extends RefExpr<DeclType> {

	@Override
	public abstract ParamDecl<DeclType> getDecl();

}
