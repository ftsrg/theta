package hu.bme.mit.inf.theta.core.decl;

import hu.bme.mit.inf.theta.core.expr.ParamRefExpr;
import hu.bme.mit.inf.theta.core.type.Type;

public interface ParamDecl<DeclType extends Type> extends Decl<DeclType, ParamDecl<DeclType>> {

	@Override
	public ParamRefExpr<DeclType> getRef();

}
