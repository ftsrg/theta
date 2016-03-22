package hu.bme.mit.inf.ttmc.formalism.sts.factory;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;

public interface STSExprFactory extends ExprFactory {

	public <T extends Type> VarRefExpr<T> Ref(final VarDecl<T> varDecl);

	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op);

}
