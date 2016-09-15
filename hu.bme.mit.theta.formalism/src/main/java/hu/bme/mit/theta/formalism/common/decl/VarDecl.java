package hu.bme.mit.theta.formalism.common.decl;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.expr.VarRefExpr;

public interface VarDecl<DeclType extends Type> extends Decl<DeclType> {

	@Override
	public VarRefExpr<DeclType> getRef();

	public IndexedConstDecl<DeclType> getConstDecl(int index);

}
