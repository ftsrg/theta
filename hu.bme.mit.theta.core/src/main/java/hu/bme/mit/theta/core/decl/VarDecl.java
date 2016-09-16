package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;

public interface VarDecl<DeclType extends Type> extends Decl<DeclType> {

	@Override
	public VarRefExpr<DeclType> getRef();

	public IndexedConstDecl<DeclType> getConstDecl(int index);

}
