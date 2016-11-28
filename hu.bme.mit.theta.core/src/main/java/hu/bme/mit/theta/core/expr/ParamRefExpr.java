package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Type;

public interface ParamRefExpr<DeclType extends Type> extends RefExpr<DeclType> {

	@Override
	ParamDecl<DeclType> getDecl();

}
