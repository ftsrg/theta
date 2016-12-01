package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.expr.ParamRefExpr;
import hu.bme.mit.theta.core.type.Type;

public interface ParamDecl<DeclType extends Type> extends Decl<DeclType> {

	@Override
	ParamRefExpr<DeclType> getRef();

}
