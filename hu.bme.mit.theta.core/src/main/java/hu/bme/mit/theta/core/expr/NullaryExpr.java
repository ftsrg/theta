package hu.bme.mit.theta.core.expr;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Type;

public abstract class NullaryExpr<ExprType extends Type> implements Expr<ExprType> {

	@Override
	public List<Expr<?>> getOps() {
		return ImmutableList.of();
	}

	@Override
	public int getArity() {
		return 0;
	}

}
