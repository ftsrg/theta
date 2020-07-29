/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.type.abstracttype;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Try;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
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
		final Expr<T> newThen = newOps.get1();
		final Expr<T> newElse = newOps.get2();
		return Exprs.Ite(cond, newThen, newElse);
	}

	/*
	 * Additive
	 */

	public static <T extends Additive<T>> AddExpr<?> Add(final Iterable<? extends Expr<?>> ops) {
		final List<Expr<?>> opList = ImmutableList.copyOf(ops);
		checkArgument(!opList.isEmpty());
		final Expr<?> head = Utils.head(opList);
		final List<Expr<?>> tail = Utils.tail(opList);
		return combineAdd(head, tail);
	}

	private static <T extends Additive<T>> AddExpr<?> combineAdd(final Expr<?> head, final List<Expr<?>> tail) {
		if (tail.isEmpty()) {
			final Expr<T> newOp = bind(head);
			final List<Expr<T>> newOps = getAddOps(newOp);
			final T type = newOp.getType();
			return type.Add(newOps);

		} else {
			final Expr<?> newHead = Utils.head(tail);
			final List<Expr<?>> newTail = Utils.tail(tail);

			final Tuple2<Expr<T>, Expr<T>> unifiedOps = unify(head, newHead);
			final Expr<T> newLeftOp = unifiedOps.get1();
			final Expr<T> newRightOp = unifiedOps.get2();
			final T type = newLeftOp.getType();

			final List<Expr<T>> newLeftOps = getAddOps(newLeftOp);
			final List<Expr<T>> newOps = ImmutableList.<Expr<T>>builder().addAll(newLeftOps).add(newRightOp).build();
			final AddExpr<T> newAddExpr = type.Add(newOps);
			return combineAdd(newAddExpr, newTail);
		}
	}

	private static <T extends Additive<T>> List<Expr<T>> getAddOps(final Expr<T> expr) {
		if (expr instanceof AddExpr) {
			final AddExpr<T> addExpr = (AddExpr<T>) expr;
			return addExpr.getOps();
		} else {
			return ImmutableList.of(expr);
		}
	}

	public static <T extends Additive<T>> SubExpr<?> Sub(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Sub(newLeftOp, newRightOp);
	}

	public static <T extends Additive<T>> NegExpr<?> Neg(final Expr<?> op) {
		final Expr<T> tOp = bind(op);
		final T type = tOp.getType();
		return type.Neg(tOp);
	}

	/*
	 * Multiplicative
	 */

	public static <T extends Multiplicative<T>> MulExpr<?> Mul(final Iterable<? extends Expr<?>> ops) {
		final List<Expr<?>> opList = ImmutableList.copyOf(ops);
		checkArgument(!opList.isEmpty());
		final Expr<?> head = Utils.head(opList);
		final List<Expr<?>> tail = Utils.tail(opList);
		return combineMul(head, tail);
	}

	private static <T extends Multiplicative<T>> MulExpr<?> combineMul(final Expr<?> head, final List<Expr<?>> tail) {
		if (tail.isEmpty()) {
			final Expr<T> newOp = bind(head);
			final List<Expr<T>> newOps = getMulOps(newOp);
			final T type = newOp.getType();
			return type.Mul(newOps);

		} else {
			final Expr<?> newHead = Utils.head(tail);
			final List<Expr<?>> newTail = Utils.tail(tail);

			final Tuple2<Expr<T>, Expr<T>> unifiedOps = unify(head, newHead);
			final Expr<T> newLeftOp = unifiedOps.get1();
			final Expr<T> newRightOp = unifiedOps.get2();
			final T type = newLeftOp.getType();

			final List<Expr<T>> newLeftOps = getMulOps(newLeftOp);
			final List<Expr<T>> newOps = ImmutableList.<Expr<T>>builder().addAll(newLeftOps).add(newRightOp).build();
			final MulExpr<T> newMulExpr = type.Mul(newOps);
			return combineMul(newMulExpr, newTail);
		}
	}

	private static <T extends Multiplicative<T>> List<Expr<T>> getMulOps(final Expr<T> expr) {
		if (expr instanceof MulExpr) {
			final MulExpr<T> mulExpr = (MulExpr<T>) expr;
			return mulExpr.getOps();
		} else {
			return ImmutableList.of(expr);
		}
	}

	public static <T extends Multiplicative<T>> DivExpr<?> Div(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Div(newLeftOp, newRightOp);
	}

	/*
	 * Divisible
	 */

	public static <T extends Divisible<T>> ModExpr<?> Mod(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Mod(newLeftOp, newRightOp);
	}

	public static <T extends Divisible<T>> RemExpr<?> Rem(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Rem(newLeftOp, newRightOp);
	}

	/*
	 * Equational
	 */

	public static <T extends Equational<T>> EqExpr<?> Eq(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Eq(newLeftOp, newRightOp);
	}

	public static <T extends Equational<T>> NeqExpr<?> Neq(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Neq(newLeftOp, newRightOp);
	}

	/*
	 * Ordered
	 */

	public static <T extends Ordered<T>> LtExpr<?> Lt(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Lt(newLeftOp, newRightOp);
	}

	public static <T extends Ordered<T>> LeqExpr<?> Leq(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Leq(newLeftOp, newRightOp);
	}

	public static <T extends Ordered<T>> GtExpr<?> Gt(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Gt(newLeftOp, newRightOp);
	}

	public static <T extends Ordered<T>> GeqExpr<?> Geq(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Tuple2<Expr<T>, Expr<T>> newOps = unify(leftOp, rightOp);
		final Expr<T> newLeftOp = newOps.get1();
		final Expr<T> newRightOp = newOps.get2();
		final T type = newLeftOp.getType();
		return type.Geq(newLeftOp, newRightOp);
	}

	/*
	 * Convenience methods
	 */

	public static <T extends Additive<T>> AddExpr<?> Add(final Expr<?> leftOp, final Expr<?> rightOp) {
		return Add(ImmutableList.of(leftOp, rightOp));
	}

	public static <T extends Multiplicative<T>> MulExpr<?> Mul(final Expr<?> leftOp, final Expr<?> rightOp) {
		return Mul(ImmutableList.of(leftOp, rightOp));
	}

	/*
	 * Helper methods
	 */

	private static <T extends Type, T1 extends Type, T2 extends Type, C extends Castable<C>> Tuple2<Expr<T>, Expr<T>> unify(
			final Expr<T1> expr1, final Expr<T2> expr2) {
		final T1 type1 = expr1.getType();
		final T2 type2 = expr2.getType();

		if (expr1.getType().equals(expr2.getType())) {
			@SuppressWarnings("unchecked") final Expr<T1> t1Expr2 = (Expr<T1>) expr2;
			return bind(expr1, t1Expr2);
		}

		if (type1 instanceof Castable) {
			@SuppressWarnings("unchecked") final C cType1 = (C) type1;
			@SuppressWarnings("unchecked") final Expr<C> cExpr1 = (Expr<C>) expr1;
			final Try<Expr<T2>> tryToCast = Try.attempt(() -> cType1.Cast(cExpr1, type2));
			if (tryToCast.isSuccess()) {
				final Expr<T2> t2Expr1 = tryToCast.asSuccess().getValue();
				return bind(t2Expr1, expr2);
			}
		}

		if (type2 instanceof Castable) {
			@SuppressWarnings("unchecked") final C cType2 = (C) type2;
			@SuppressWarnings("unchecked") final Expr<C> cExpr2 = (Expr<C>) expr2;
			final Try<Expr<T1>> tryToCast = Try.attempt(() -> cType2.Cast(cExpr2, type1));
			if (tryToCast.isSuccess()) {
				final Expr<T1> t1Expr2 = tryToCast.asSuccess().getValue();
				return bind(expr1, t1Expr2);
			}
		}

		throw new ClassCastException("Types " + expr1.getType() + " and " + expr2.getType() + " can not be unified");
	}

	private static <TR extends Type, TP extends Type> Expr<TR> bind(final Expr<TP> expr) {
		@SuppressWarnings("unchecked") final Expr<TR> trExpr = (Expr<TR>) expr;
		return trExpr;
	}

	private static <TR extends Type, TP extends Type> Tuple2<Expr<TR>, Expr<TR>> bind(final Expr<TP> expr1,
																					  final Expr<TP> expr2) {
		@SuppressWarnings("unchecked") final Expr<TR> trExpr1 = (Expr<TR>) expr1;
		@SuppressWarnings("unchecked") final Expr<TR> trExpr2 = (Expr<TR>) expr2;
		return Tuple2.of(trExpr1, trExpr2);
	}

}
