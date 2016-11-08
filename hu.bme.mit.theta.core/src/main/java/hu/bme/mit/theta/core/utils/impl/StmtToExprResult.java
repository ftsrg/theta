package hu.bme.mit.theta.core.utils.impl;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public final class StmtToExprResult {
	final Collection<Expr<? extends BoolType>> exprs;
	final VarIndexing indexing;

	private StmtToExprResult(final Iterable<? extends Expr<? extends BoolType>> exprs, final VarIndexing indexing) {
		this.exprs = ImmutableList.copyOf(exprs);
		this.indexing = indexing;
	}

	static StmtToExprResult of(final Iterable<? extends Expr<? extends BoolType>> exprs, final VarIndexing indexing) {
		return new StmtToExprResult(exprs, indexing);
	}

	public Collection<? extends Expr<? extends BoolType>> getExprs() {
		return exprs;
	}

	public VarIndexing getIndexing() {
		return indexing;
	}
}