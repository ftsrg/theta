package hu.bme.mit.inf.ttmc.core.decl;

import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface ParamDecl<DeclType extends Type> extends Decl<DeclType, ParamDecl<DeclType>> {

	@Override
	public ParamRefExpr<DeclType> getRef();

}
