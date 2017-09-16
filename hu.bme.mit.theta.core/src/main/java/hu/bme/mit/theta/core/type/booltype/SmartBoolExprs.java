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
package hu.bme.mit.theta.core.type.booltype;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;

public final class SmartBoolExprs {

	private SmartBoolExprs() {
	}

	public static Expr<BoolType> Not(final Expr<BoolType> op) {
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

	public static Expr<BoolType> And(final Collection<? extends Expr<BoolType>> ops) {
		if (ops.isEmpty()) {
			return BoolExprs.True();
		} else if (ops.contains(BoolExprs.False())) {
			return BoolExprs.False();
		}

		final List<Expr<BoolType>> filteredOps = ops.stream().filter(o -> !o.equals(BoolExprs.True()))
				.collect(Collectors.toList());

		if (filteredOps.isEmpty()) {
			return BoolExprs.True();
		} else if (filteredOps.size() == 1) {
			return Utils.anyElementOf(filteredOps);
		} else {
			return BoolExprs.And(filteredOps);
		}
	}

	public static Expr<BoolType> Or(final Collection<? extends Expr<BoolType>> ops) {
		if (ops.isEmpty()) {
			return BoolExprs.True();
		} else if (ops.contains(BoolExprs.True())) {
			return BoolExprs.True();
		}

		final List<Expr<BoolType>> filteredOps = ops.stream().filter(o -> !o.equals(BoolExprs.False()))
				.collect(Collectors.toList());

		if (filteredOps.isEmpty()) {
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

	public static Expr<BoolType> And(final Expr<BoolType> op1, final Expr<BoolType> op2) {
		return And(ImmutableSet.of(op1, op2));
	}

	public static Expr<BoolType> And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3) {
		return And(ImmutableSet.of(op1, op2, op3));
	}

	public static Expr<BoolType> And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
			final Expr<BoolType> op4) {
		return And(ImmutableSet.of(op1, op2, op3, op4));
	}

	public static Expr<BoolType> And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
			final Expr<BoolType> op4, final Expr<BoolType> op5) {
		return And(ImmutableSet.of(op1, op2, op3, op4, op5));
	}

	////

	public static Expr<BoolType> Or(final Expr<BoolType> op1, final Expr<BoolType> op2) {
		return Or(ImmutableSet.of(op1, op2));
	}

	public static Expr<BoolType> Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3) {
		return Or(ImmutableSet.of(op1, op2, op3));
	}

	public static Expr<BoolType> Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
			final Expr<BoolType> op4) {
		return Or(ImmutableSet.of(op1, op2, op3, op4));
	}

	public static Expr<BoolType> Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
			final Expr<BoolType> op4, final Expr<BoolType> op5) {
		return Or(ImmutableSet.of(op1, op2, op3, op4, op5));
	}
}
