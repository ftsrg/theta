package hu.bme.mit.theta.core.type.abstracttype;

import static com.google.common.collect.ImmutableList.of;

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

	public static <T extends Additive<T>> SubExpr<?> Sub(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps._1();
		final Expr<T> newRightOp = newOps._2();
		final T type = newLeftOp.getType();
		return type.Sub(newLeftOp, newRightOp);
	}

	public static <T extends Additive<T>> NegExpr<?> Neg(final Expr<?> op) {
		final Expr<T> newOp = bind(op);
		final T type = newOp.getType();
		return type.Neg(newOp);
	}

	/*
	 * Multiplicative
	 */

	public static <T extends Multiplicative<T>> MulExpr<?> Mul(final Iterable<? extends Expr<?>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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
	 * Convenience methods
	 */

	public static AddExpr<?> Add(final Expr<?> op1, final Expr<?> op2) {
		return Add(of(op1, op2));
	}

	public static MulExpr<?> Mul(final Expr<?> op1, final Expr<?> op2) {
		return Mul(of(op1, op2));
	}

	/*
	 * Helper methods
	 */

	@SuppressWarnings("unchecked")
	private static <T extends Type> Expr<T> bind(final Expr<?> expr) {
		return (Expr<T>) expr;
	}

	private static <T extends Type, T1 extends Type, T2 extends Type, CT extends Castable<CT>> Tuple2<Expr<T>, Expr<T>> unify(
			final Expr<T1> expr1, final Expr<T2> expr2) {
		final T1 type1 = expr1.getType();
		final T2 type2 = expr2.getType();

		if (expr1.getType().equals(expr2.getType())) {
			return Tuple.of(bind(expr1), bind(expr2));
		}

		if (type1 instanceof Castable) {
			@SuppressWarnings("unchecked")
			final CT cType1 = (CT) type1;
			final Expr<CT> cExpr1 = bind(expr1);
			final Try<Expr<T2>> tryToCast = Try.attempt(() -> cType1.Cast(cExpr1, type2));
			if (tryToCast.isSuccess()) {
				final Expr<T2> result = tryToCast.asSuccess().getValue();
				return Tuple.of(bind(result), bind(expr2));
			}
		}

		if (type2 instanceof Castable) {
			@SuppressWarnings("unchecked")
			final CT cType2 = (CT) type2;
			final Expr<CT> cExpr2 = bind(expr2);
			final Try<Expr<T1>> tryToCast = Try.attempt(() -> cType2.Cast(cExpr2, type1));
			if (tryToCast.isSuccess()) {
				final Expr<T1> result = tryToCast.asSuccess().getValue();
				return Tuple.of(bind(expr1), bind(result));
			}
		}

		throw new ClassCastException("Types " + expr1.getType() + " and " + expr2.getType() + " can not be unifyed");
	}

}
