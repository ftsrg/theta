package hu.bme.mit.theta.core.expr;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.BoolType;

public final class SmartExprs {

	private SmartExprs() {
	}

	public static Expr<? extends BoolType> Not(final Expr<? extends BoolType> op) {
		if (op.equals(Exprs.True())) {
			return Exprs.False();
		} else if (op.equals(Exprs.False())) {
			return Exprs.True();
		} else if (op instanceof NotExpr) {
			return ((NotExpr) op).getOp();
		} else {
			return Exprs.Not(op);
		}
	}

	public static Expr<? extends BoolType> And(final Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops.size() == 0) {
			return Exprs.True();
		} else if (ops.contains(Exprs.False())) {
			return Exprs.False();
		}

		final List<Expr<? extends BoolType>> filteredOps = ops.stream().filter(o -> !o.equals(Exprs.True()))
				.collect(Collectors.toList());

		if (filteredOps.size() == 0) {
			return Exprs.True();
		} else if (filteredOps.size() == 1) {
			return Utils.anyElementOf(filteredOps);
		} else {
			return Exprs.And(filteredOps);
		}
	}

	public static Expr<? extends BoolType> Or(final Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops.size() == 0) {
			return Exprs.True();
		} else if (ops.contains(Exprs.True())) {
			return Exprs.True();
		}

		final List<Expr<? extends BoolType>> filteredOps = ops.stream().filter(o -> !o.equals(Exprs.False()))
				.collect(Collectors.toList());

		if (filteredOps.size() == 0) {
			return Exprs.False();
		} else if (filteredOps.size() == 1) {
			return Utils.anyElementOf(filteredOps);
		} else {
			return Exprs.Or(filteredOps);
		}
	}

	/*
	 * Convenience methods
	 */

	public static Expr<? extends BoolType> And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2) {
		return And(ImmutableSet.of(op1, op2));
	}

	public static Expr<? extends BoolType> And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3) {
		return And(ImmutableSet.of(op1, op2, op3));
	}

	public static Expr<? extends BoolType> And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4) {
		return And(ImmutableSet.of(op1, op2, op3, op4));
	}

	public static Expr<? extends BoolType> And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4,
			final Expr<? extends BoolType> op5) {
		return And(ImmutableSet.of(op1, op2, op3, op4, op5));
	}

	////

	public static Expr<? extends BoolType> Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2) {
		return Or(ImmutableSet.of(op1, op2));
	}

	public static Expr<? extends BoolType> Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3) {
		return Or(ImmutableSet.of(op1, op2, op3));
	}

	public static Expr<? extends BoolType> Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4) {
		return Or(ImmutableSet.of(op1, op2, op3, op4));
	}

	public static Expr<? extends BoolType> Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4,
			final Expr<? extends BoolType> op5) {
		return Or(ImmutableSet.of(op1, op2, op3, op4, op5));
	}
}
