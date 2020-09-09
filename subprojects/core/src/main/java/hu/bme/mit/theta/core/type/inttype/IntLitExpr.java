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
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;

import java.math.BigInteger;

public final class IntLitExpr extends NullaryExpr<IntType> implements LitExpr<IntType>, Comparable<IntLitExpr> {

	private static final int HASH_SEED = 4111;
	private volatile int hashCode = 0;

	private final BigInteger value;

	private IntLitExpr(final BigInteger value) {
		this.value = value;
	}

	public static IntLitExpr of(final BigInteger value) {
		return new IntLitExpr(value);
	}

	public BigInteger getValue() {
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

	public IntLitExpr add(final IntLitExpr that) {
		return IntLitExpr.of(this.value.add(that.value));
	}

	public IntLitExpr sub(final IntLitExpr that) {
		return IntLitExpr.of(this.value.subtract(that.value));
	}

	public IntLitExpr neg() {
		return IntLitExpr.of(this.value.negate());
	}

	public IntLitExpr pos() {
		return IntLitExpr.of(this.value);
	}

	public IntLitExpr div(final IntLitExpr that) {
		return IntLitExpr.of(this.value.divide(that.value));
	}

	public IntLitExpr mod(final IntLitExpr that) {
		// Always positive semantics:
		// 5 mod 3 = 2
		// 5 mod -3 = 2
		// -5 mod 3 = 1
		// -5 mod -3 = 1
		var result = this.value.mod(that.value.abs());
		if (result.compareTo(BigInteger.ZERO) < 0) {
			result = result.add(that.value.abs());
		}
		assert result.compareTo(BigInteger.ZERO) >= 0;
		return IntLitExpr.of(result);
	}

	public IntLitExpr rem(final IntLitExpr that) {
		// Semantics:
		// 5 rem 3 = 2
		// 5 rem -3 = -2
		// -5 rem 3 = 1
		// -5 rem -3 = -1
		final var thisAbs = this.value.abs();
		final var thatAbs = that.value.abs();
		if (this.value.compareTo(BigInteger.ZERO) < 0 && that.value.compareTo(BigInteger.ZERO) < 0) {
			var result = thisAbs.mod(thatAbs);
			if (result.compareTo(BigInteger.ZERO) != 0) {
				result = result.subtract(thatAbs);
			}
			return new IntLitExpr(result);
		} else if (this.value.compareTo(BigInteger.ZERO) >= 0 && that.value.compareTo(BigInteger.ZERO) < 0) {
			return new IntLitExpr(thisAbs.mod(thatAbs).negate());
		} else if (this.value.compareTo(BigInteger.ZERO) < 0 && that.value.compareTo(BigInteger.ZERO) >= 0) {
			var result = thisAbs.mod(thatAbs);
			if (result.compareTo(BigInteger.ZERO) != 0) {
				result = thatAbs.subtract(result);
			}
			return IntLitExpr.of(result);
		} else {
			return IntLitExpr.of(this.value.mod(that.value));
		}
	}

	public BoolLitExpr eq(final IntLitExpr that) {
		return Bool(this.value.compareTo(that.value) == 0);
	}

	public BoolLitExpr neq(final IntLitExpr that) {
		return Bool(this.value.compareTo(that.value) != 0);
	}

	public BoolLitExpr lt(final IntLitExpr that) {
		return Bool(this.value.compareTo(that.value) < 0);
	}

	public BoolLitExpr leq(final IntLitExpr that) {
		return Bool(this.value.compareTo(that.value) <= 0);
	}

	public BoolLitExpr gt(final IntLitExpr that) {
		return Bool(this.value.compareTo(that.value) > 0);
	}

	public BoolLitExpr geq(final IntLitExpr that) {
		return Bool(this.value.compareTo(that.value) >= 0);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + value.hashCode();
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
			return this.getValue().compareTo(that.getValue()) == 0;
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return getValue().toString();
	}

	@Override
	public int compareTo(final IntLitExpr that) {
		return this.getValue().compareTo(that.getValue());
	}

}
