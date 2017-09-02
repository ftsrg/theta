package hu.bme.mit.theta.core.utils;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class StmtUnfoldResult {
	final Collection<Expr<BoolType>> exprs;
	final VarIndexing indexing;

	private StmtUnfoldResult(final Iterable<? extends Expr<BoolType>> exprs, final VarIndexing indexing) {
		this.exprs = ImmutableList.copyOf(exprs);
		this.indexing = indexing;
	}

	public static StmtUnfoldResult of(final Iterable<? extends Expr<BoolType>> exprs, final VarIndexing indexing) {
		return new StmtUnfoldResult(exprs, indexing);
	}

	public Collection<? extends Expr<BoolType>> getExprs() {
		return exprs;
	}

	public VarIndexing getIndexing() {
		return indexing;
	}
}