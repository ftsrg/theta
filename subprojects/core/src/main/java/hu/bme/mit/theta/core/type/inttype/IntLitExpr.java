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
package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;

import java.math.BigInteger;

public final class IntLitExpr extends NullaryExpr<IntType> implements LitExpr<IntType>, Comparable<IntLitExpr> {

	private static final int HASH_SEED = 4111;
	private volatile int hashCode = 0;

	private final int value;

	private IntLitExpr(final int value) {
		this.value = value;
	}

	public static IntLitExpr of(final int value) {
		return new IntLitExpr(value);
	}

	public int getValue() {
		return value;
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntLitExpr eval(final Valuation val) {
		return this;
	}

	public RatLitExpr toRat() {
		return Rat(this.value, 1);
	}

	public BvLitExpr toBv(int size, boolean isSigned) {
		BigInteger res = BigInteger.valueOf(value);
		BigInteger fittedRes = BvUtils.fitBigIntegerIntoDomain(res, size, isSigned);

		if(res.equals(fittedRes)) {
			return BvUtils.bigIntegerToBvLitExpr(fittedRes, size, isSigned);
		} else {
			throw new IllegalArgumentException("The value of int " + res.toString() + " does not fit the bitvector " + (isSigned ? "signed" : "unsigned") + " domain of size " + size + " bits");
		}
	}

	public IntLitExpr add(final IntLitExpr that) {
		return IntLitExpr.of(this.value + that.value);
	}

	public IntLitExpr sub(final IntLitExpr that) {
		return IntLitExpr.of(this.value - that.value);
	}

	public IntLitExpr neg() {
		return IntLitExpr.of(-this.value);
	}

	public IntLitExpr div(final IntLitExpr that) {
		return IntLitExpr.of(this.value / that.value);
	}

	public IntLitExpr mod(final IntLitExpr that) {
		// Always positive semantics:
		// 5 mod 3 = 2
		// 5 mod -3 = 2
		// -5 mod 3 = 1
		// -5 mod -3 = 1
		int result = this.value % that.value;
		if (result < 0) {
			result += Math.abs(that.value);
		}
		assert result >= 0;
		return IntLitExpr.of(result);
	}

	public IntLitExpr rem(final IntLitExpr that) {
		// Semantics:
		// 5 rem 3 = 2
		// 5 rem -3 = -2
		// -5 rem 3 = 1
		// -5 rem -3 = -1
		final int thisAbs = Math.abs(this.value);
		final int thatAbs = Math.abs(that.value);
		if (this.value < 0 && that.value < 0) {
			int result = thisAbs % thatAbs;
			if (result != 0) {
				result -= thatAbs;
			}
			return new IntLitExpr(result);
		} else if (this.value >= 0 && that.value < 0) {
			return new IntLitExpr(-(thisAbs % thatAbs));
		} else if (this.value < 0 && that.value >= 0) {
			int result = thisAbs % thatAbs;
			if (result != 0) {
				result = thatAbs - result;
			}
			return IntLitExpr.of(result);
		} else {
			return IntLitExpr.of(this.value % that.value);
		}
	}

	public BoolLitExpr eq(final IntLitExpr that) {
		return Bool(this.value == that.value);
	}

	public BoolLitExpr neq(final IntLitExpr that) {
		return Bool(this.value != that.value);
	}

	public BoolLitExpr lt(final IntLitExpr that) {
		return Bool(this.value < that.value);
	}

	public BoolLitExpr leq(final IntLitExpr that) {
		return Bool(this.value <= that.value);
	}

	public BoolLitExpr gt(final IntLitExpr that) {
		return Bool(this.value > that.value);
	}

	public BoolLitExpr geq(final IntLitExpr that) {
		return Bool(this.value >= that.value);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + value;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntLitExpr) {
			final IntLitExpr that = (IntLitExpr) obj;
			return this.getValue() == that.getValue();
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Long.toString(getValue());
	}

	@Override
	public int compareTo(final IntLitExpr that) {
		return Long.compare(this.getValue(), that.getValue());
	}

}
