package hu.bme.mit.inf.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.MultiaryExpr;
import hu.bme.mit.inf.theta.core.type.Type;

public interface MultiaryExpr<OpsType extends Type, ExprType extends Type> extends Expr<ExprType> {
	public Collection<? extends Expr<? extends OpsType>> getOps();
	public MultiaryExpr<OpsType, ExprType> withOps(final Collection<? extends Expr<? extends OpsType>> ops);
}
