package hu.bme.mit.inf.theta.core.decl;

import hu.bme.mit.inf.theta.core.expr.ConstRefExpr;
import hu.bme.mit.inf.theta.core.type.Type;

public interface ConstDecl<DeclType extends Type> extends Decl<DeclType, ConstDecl<DeclType>> {

	@Override
	public ConstRefExpr<DeclType> getRef();

}
