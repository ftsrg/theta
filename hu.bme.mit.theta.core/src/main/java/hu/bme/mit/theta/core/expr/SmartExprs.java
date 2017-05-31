package hu.bme.mit.theta.core.expr;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.NotExpr;

public final class SmartExprs {

	private SmartExprs() {
	}

	public static Expr<? extends BoolType> Not(final Expr<? extends BoolType> op) {
		if (op.equals(BoolExprs.True())) {
			return BoolExprs.False();
		} else if (op.equals(BoolExprs.False())) {
			return BoolExprs.True();
		} else if (op instanceof NotExpr) {
			return ((NotExpr) op).getOp();
		} else {
			return BoolExprs.Not(op);
		}
	}

	public static Expr<? extends BoolType> And(final Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops.size() == 0) {
			return BoolExprs.True();
		} else if (ops.contains(BoolExprs.False())) {
			return BoolExprs.False();
		}

		final List<Expr<? extends BoolType>> filteredOps = ops.stream().filter(o -> !o.equals(BoolExprs.True()))
				.collect(Collectors.toList());

		if (filteredOps.size() == 0) {
			return BoolExprs.True();
		} else if (filteredOps.size() == 1) {
			return Utils.anyElementOf(filteredOps);
		} else {
			return BoolExprs.And(filteredOps);
		}
	}

	public static Expr<? extends BoolType> Or(final Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops.size() == 0) {
			return BoolExprs.True();
		} else if (ops.contains(BoolExprs.True())) {
			return BoolExprs.True();
		}

		final List<Expr<? extends BoolType>> filteredOps = ops.stream().filter(o -> !o.equals(BoolExprs.False()))
				.collect(Collectors.toList());

		if (filteredOps.size() == 0) {
			return BoolExprs.False();
		} else if (filteredOps.size() == 1) {
			return Utils.anyElementOf(filteredOps);
		} else {
			return BoolExprs.Or(filteredOps);
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
