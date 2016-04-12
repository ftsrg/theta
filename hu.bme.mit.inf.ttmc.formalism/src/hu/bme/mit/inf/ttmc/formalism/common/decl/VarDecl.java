package hu.bme.mit.inf.ttmc.formalism.common.decl;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;

public interface VarDecl<DeclType extends Type> extends Decl<DeclType, VarDecl<DeclType>> {

	@Override
	public VarRefExpr<DeclType> getRef();
}
