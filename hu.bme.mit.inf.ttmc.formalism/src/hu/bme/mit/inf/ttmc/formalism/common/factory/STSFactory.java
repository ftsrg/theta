package hu.bme.mit.inf.ttmc.formalism.common.factory;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;

public interface STSFactory extends VarDeclFactory {
	
	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op);
}
