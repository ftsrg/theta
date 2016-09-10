package hu.bme.mit.theta.formalism.common.decl;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.expr.IndexedConstRefExpr;

public interface IndexedConstDecl<DeclType extends Type> extends ConstDecl<DeclType> {

	@Override
	public IndexedConstRefExpr<DeclType> getRef();

	public VarDecl<DeclType> getVarDecl();

	public int getIndex();

}
