package hu.bme.mit.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.theta.core.type.Type;

public interface MultiaryExpr<OpsType extends Type, ExprType extends Type> extends Expr<ExprType> {
	Collection<? extends Expr<? extends OpsType>> getOps();

	MultiaryExpr<OpsType, ExprType> withOps(final Collection<? extends Expr<? extends OpsType>> ops);
}
