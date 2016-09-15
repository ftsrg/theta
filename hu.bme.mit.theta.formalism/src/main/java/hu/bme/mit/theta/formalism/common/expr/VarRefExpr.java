package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;

public interface VarRefExpr<DeclType extends Type> extends RefExpr<DeclType> {

	@Override
	public VarDecl<DeclType> getDecl();

}
