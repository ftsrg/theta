package hu.bme.mit.inf.ttmc.formalism.factory;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.expr.PrimedExpr;

public interface STSFactory {
	
	public <T extends Type> VarDecl<T> Var(final String name, final T type);

	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op);
}
