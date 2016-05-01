package hu.bme.mit.inf.ttmc.core.decl;

import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface ConstDecl<DeclType extends Type> extends Decl<DeclType, ConstDecl<DeclType>> {

	@Override
	public ConstRefExpr<DeclType> getRef();

}
