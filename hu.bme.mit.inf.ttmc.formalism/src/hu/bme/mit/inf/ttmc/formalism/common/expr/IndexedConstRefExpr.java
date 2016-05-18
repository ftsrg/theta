package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.IndexedConstDecl;

public interface IndexedConstRefExpr<DeclType extends Type> extends ConstRefExpr<DeclType> {

	@Override
	public IndexedConstDecl<DeclType> getDecl();
}
