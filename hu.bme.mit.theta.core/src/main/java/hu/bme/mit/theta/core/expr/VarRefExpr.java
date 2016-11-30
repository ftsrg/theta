package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public interface VarRefExpr<DeclType extends Type> extends RefExpr<DeclType> {

	@Override
	VarDecl<DeclType> getDecl();

}
