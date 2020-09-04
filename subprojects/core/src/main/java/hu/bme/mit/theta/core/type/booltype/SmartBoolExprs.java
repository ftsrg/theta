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

import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.common.Utils.singleElementOf;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Expr;

public final class SmartBoolExprs {

	private SmartBoolExprs() {
	}

	public static Expr<BoolType> Not(final Expr<BoolType> op) {
		if (op.equals(True())) {
			return False();
		} else if (op.equals(False())) {
			return True();
		} else if (op instanceof NotExpr) {
			return ((NotExpr) op).getOp();
		} else {
			return BoolExprs.Not(op);
		}
	}

	public static Expr<BoolType> Imply(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		if (leftOp.equals(False())) {
			return True();
		} else if (leftOp.equals(True())) {
			return rightOp;
		} else if (rightOp.equals(False())) {
			return Not(leftOp);
		} else if (rightOp.equals(True())) {
			return True();
		} else {
			return BoolExprs.Imply(leftOp, rightOp);
		}
	}

	public static Expr<BoolType> And(final Collection<? extends Expr<BoolType>> ops) {
		if (ops.isEmpty()) {
			return True();
		} else if (ops.contains(False())) {
			return False();
		}

		final List<Expr<BoolType>> filteredOps = ops.stream().filter(o -> !o.equals(True())).collect(toImmutableList());

		if (filteredOps.isEmpty()) {
			return True();
		} else if (filteredOps.size() == 1) {
			return singleElementOf(filteredOps);
		} else {
			return BoolExprs.And(filteredOps);
		}
	}

	public static Expr<BoolType> Or(final Collection<? extends Expr<BoolType>> ops) {
		if (ops.isEmpty()) {
			return False();
		} else if (ops.contains(True())) {
			return True();
		}

		final List<Expr<BoolType>> filteredOps = ops.stream().filter(o -> !o.equals(False()))
				.collect(toImmutableList());

		if (filteredOps.isEmpty()) {
			return False();
		} else if (filteredOps.size() == 1) {
			return singleElementOf(filteredOps);
		} else {
			return BoolExprs.Or(filteredOps);
		}
	}

	/*
	 * Convenience methods
	 */

	public static Expr<BoolType> And(final Expr<BoolType> op1, final Expr<BoolType> op2) {
		return And(ImmutableList.of(op1, op2));
	}

	public static Expr<BoolType> And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3) {
		return And(ImmutableList.of(op1, op2, op3));
	}

	public static Expr<BoolType> And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
									 final Expr<BoolType> op4) {
		return And(ImmutableList.of(op1, op2, op3, op4));
	}

	public static Expr<BoolType> And(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
									 final Expr<BoolType> op4, final Expr<BoolType> op5) {
		return And(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static Expr<BoolType> Or(final Expr<BoolType> op1, final Expr<BoolType> op2) {
		return Or(ImmutableList.of(op1, op2));
	}

	public static Expr<BoolType> Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3) {
		return Or(ImmutableList.of(op1, op2, op3));
	}

	public static Expr<BoolType> Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
									final Expr<BoolType> op4) {
		return Or(ImmutableList.of(op1, op2, op3, op4));
	}

	public static Expr<BoolType> Or(final Expr<BoolType> op1, final Expr<BoolType> op2, final Expr<BoolType> op3,
									final Expr<BoolType> op4, final Expr<BoolType> op5) {
		return Or(ImmutableList.of(op1, op2, op3, op4, op5));
	}
}
