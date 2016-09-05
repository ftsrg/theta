package hu.bme.mit.inf.theta.formalism.common.expr;

import hu.bme.mit.inf.theta.core.expr.ConstRefExpr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.IndexedConstDecl;

public interface IndexedConstRefExpr<DeclType extends Type> extends ConstRefExpr<DeclType> {

	@Override
	public IndexedConstDecl<DeclType> getDecl();
}
