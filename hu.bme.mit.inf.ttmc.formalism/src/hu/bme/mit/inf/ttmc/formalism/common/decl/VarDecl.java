package hu.bme.mit.inf.ttmc.formalism.common.decl;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;

public interface VarDecl<DeclType extends Type> extends Decl<DeclType> {

	@Override
	public VarRefExpr<DeclType> getRef();
}
