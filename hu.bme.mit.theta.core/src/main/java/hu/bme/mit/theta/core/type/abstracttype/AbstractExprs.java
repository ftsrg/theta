package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.common.Try;
import hu.bme.mit.theta.common.Tuple;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.anytype.Exprs;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class AbstractExprs {

	private AbstractExprs() {
	}

	/*
	 * General
	 */

	public static <T extends Type> IteExpr<?> Ite(final Expr<BoolType> cond, final Expr<?> then, final Expr<?> elze) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(then, elze);
		final Expr<T> newThen = newOps._1();
		final Expr<T> newElse = newOps._2();
		return Exprs.Ite(cond, newThen, newElse);
	}

	/*
	 * Additive
	 */

	public static <T extends Additive<T>> AddExpr<?> Add(final Iterable<? extends Expr<?>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static <T extends Additive<T>> AddExpr<?> Add(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Add(newLeftOp, newRightOp);
	}

	public static <T extends Additive<T>> SubExpr<?> Sub(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Sub(newLeftOp, newRightOp);
	}

	public static <T extends Additive<T>> NegExpr<?> Neg(final Expr<?> op) {
		final Type type = op.getType();
		@SuppressWarnings("unchecked")
		final T tType = (T) type;
		@SuppressWarnings("unchecked")
		final Expr<T> tOp = (Expr<T>) op;
		return tType.Neg(tOp);
	}

	/*
	 * Multiplicative
	 */

	public static <T extends Multiplicative<T>> MulExpr<?> Mul(final Iterable<? extends Expr<?>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static <T extends Multiplicative<T>> MulExpr<?> Mul(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Mul(newLeftOp, newRightOp);
	}

	public static <T extends Multiplicative<T>> DivExpr<?> Div(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Div(newLeftOp, newRightOp);
	}

	/*
	 * Equational
	 */

	public static <T extends Equational<T>> EqExpr<?> Eq(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Eq(newLeftOp, newRightOp);
	}

	public static <T extends Equational<T>> NeqExpr<?> Neq(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Neq(newLeftOp, newRightOp);
	}

	/*
	 * Ordered
	 */

	public static <T extends Ordered<T>> LtExpr<?> Lt(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Lt(newLeftOp, newRightOp);
	}

	public static <T extends Ordered<T>> LeqExpr<?> Leq(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Leq(newLeftOp, newRightOp);
	}

	public static <T extends Ordered<T>> GtExpr<?> Gt(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Gt(newLeftOp, newRightOp);
	}

	public static <T extends Ordered<T>> GeqExpr<?> Geq(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Geq(newLeftOp, newRightOp);
	}

	/*
	 * Helper methods
	 */

	private static <T extends Type, T1 extends Type, T2 extends Type, C extends Castable<C>> Tuple2<Expr<T>, Expr<T>> unify(
			final Expr<T1> expr1, final Expr<T2> expr2) {
		final T1 type1 = expr1.getType();
		final T2 type2 = expr2.getType();

		if (expr1.getType().equals(expr2.getType())) {
			@SuppressWarnings("unchecked")
			final Expr<T1> t1Expr2 = (Expr<T1>) expr2;
			return bind(expr1, t1Expr2);
		}

		if (type1 instanceof Castable) {
			@SuppressWarnings("unchecked")
			final C cType1 = (C) type1;
			@SuppressWarnings("unchecked")
			final Expr<C> cExpr1 = (Expr<C>) expr1;
			final Try<Expr<T2>> tryToCast = Try.attempt(() -> cType1.Cast(cExpr1, type2));
			if (tryToCast.isSuccess()) {
				final Expr<T2> t2Expr1 = tryToCast.asSuccess().getValue();
				return bind(t2Expr1, expr2);
			}
		}

		if (type2 instanceof Castable) {
			@SuppressWarnings("unchecked")
			final C cType2 = (C) type2;
			@SuppressWarnings("unchecked")
			final Expr<C> cExpr2 = (Expr<C>) expr2;
			final Try<Expr<T1>> tryToCast = Try.attempt(() -> cType2.Cast(cExpr2, type1));
			if (tryToCast.isSuccess()) {
				final Expr<T1> t1Expr2 = tryToCast.asSuccess().getValue();
				return bind(expr1, t1Expr2);
			}
		}

		throw new ClassCastException("Types " + expr1.getType() + " and " + expr2.getType() + " can not be unified");
	}

	private static <TR extends Type, TP extends Type> Tuple2<Expr<TR>, Expr<TR>> bind(final Expr<TP> expr1,
			final Expr<TP> expr2) {
		@SuppressWarnings("unchecked")
		final Expr<TR> trExpr1 = (Expr<TR>) expr1;
		@SuppressWarnings("unchecked")
		final Expr<TR> trExpr2 = (Expr<TR>) expr2;
		return Tuple.of(trExpr1, trExpr2);
	}

}
