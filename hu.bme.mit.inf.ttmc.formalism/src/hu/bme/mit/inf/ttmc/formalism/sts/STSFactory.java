package hu.bme.mit.inf.ttmc.formalism.sts;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;

public interface STSFactory extends VarDeclFactory {
	
	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op);
}
