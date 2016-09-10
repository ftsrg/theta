package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.decl.IndexedConstDecl;

public interface IndexedConstRefExpr<DeclType extends Type> extends ConstRefExpr<DeclType> {

	@Override
	public IndexedConstDecl<DeclType> getDecl();
}
