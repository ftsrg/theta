package hu.bme.mit.theta.core.expr;

import java.util.List;

import hu.bme.mit.theta.core.type.Type;

public interface Expr<ExprType extends Type> {

	ExprType getType();

	int getArity();

	List<? extends Expr<?>> getOps();

	Expr<ExprType> withOps(List<? extends Expr<?>> ops);

}