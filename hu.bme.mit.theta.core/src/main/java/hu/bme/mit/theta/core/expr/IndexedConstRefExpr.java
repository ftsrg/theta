package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.type.Type;

public interface IndexedConstRefExpr<DeclType extends Type> extends ConstRefExpr<DeclType> {

	@Override
	IndexedConstDecl<DeclType> getDecl();
}
