package hu.bme.mit.theta.core.utils;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class UnfoldResult {
	final Collection<Expr<BoolType>> exprs;
	final VarIndexing indexing;

	private UnfoldResult(final Iterable<? extends Expr<BoolType>> exprs, final VarIndexing indexing) {
		this.exprs = ImmutableList.copyOf(exprs);
		this.indexing = indexing;
	}

	public static UnfoldResult of(final Iterable<? extends Expr<BoolType>> exprs, final VarIndexing indexing) {
		return new UnfoldResult(exprs, indexing);
	}

	public Collection<? extends Expr<BoolType>> getExprs() {
		return exprs;
	}

	public VarIndexing getIndexing() {
		return indexing;
	}
}