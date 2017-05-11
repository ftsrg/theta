package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.type.Type;

public abstract class IndexedConstRefExpr<DeclType extends Type> extends ConstRefExpr<DeclType> {

	@Override
	public abstract IndexedConstDecl<DeclType> getDecl();
}
