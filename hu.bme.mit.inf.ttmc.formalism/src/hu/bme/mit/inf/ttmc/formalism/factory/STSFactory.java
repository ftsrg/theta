package hu.bme.mit.inf.ttmc.formalism.factory;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.expr.PrimedExpr;

public interface STSFactory extends VarFactory {
	
	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op);
}
