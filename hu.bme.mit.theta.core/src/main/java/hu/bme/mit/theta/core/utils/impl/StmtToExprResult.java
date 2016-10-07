package hu.bme.mit.theta.core.utils.impl;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public final class StmtToExprResult {
	final Collection<Expr<? extends BoolType>> exprs;
	final VarIndexes indexes;

	private StmtToExprResult(final Collection<? extends Expr<? extends BoolType>> exprs, final VarIndexes indexes) {
		this.exprs = ImmutableList.copyOf(exprs);
		this.indexes = indexes;
	}

	static StmtToExprResult of(final Collection<? extends Expr<? extends BoolType>> exprs, final VarIndexes indexes) {
		return new StmtToExprResult(exprs, indexes);
	}

	public Collection<? extends Expr<? extends BoolType>> getExprs() {
		return exprs;
	}

	public VarIndexes getIndexes() {
		return indexes;
	}
}