package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.expr.IndexedConstRefExpr;
import hu.bme.mit.theta.core.type.Type;

public interface IndexedConstDecl<DeclType extends Type> extends ConstDecl<DeclType> {

	@Override
	IndexedConstRefExpr<DeclType> getRef();

	VarDecl<DeclType> getVarDecl();

	int getIndex();

}
