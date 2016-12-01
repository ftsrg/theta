package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.type.Type;

public interface ConstDecl<DeclType extends Type> extends Decl<DeclType> {

	@Override
	ConstRefExpr<DeclType> getRef();

}
