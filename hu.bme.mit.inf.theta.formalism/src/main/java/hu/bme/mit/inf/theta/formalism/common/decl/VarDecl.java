package hu.bme.mit.inf.theta.formalism.common.decl;

import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.expr.VarRefExpr;

public interface VarDecl<DeclType extends Type> extends Decl<DeclType, VarDecl<DeclType>> {

	@Override
	public VarRefExpr<DeclType> getRef();

	public IndexedConstDecl<DeclType> getConstDecl(int index);

}
