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
package hu.bme.mit.theta.core.type.rattype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;

import java.math.BigInteger;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

public final class RatLitExpr extends NullaryExpr<RatType> implements LitExpr<RatType>, Comparable<RatLitExpr> {

	private static final int HASH_SEED = 149;

	private final BigInteger num;
	private final BigInteger denom;

	private volatile int hashCode = 0;

	private RatLitExpr(final BigInteger num, final BigInteger denom) {
		checkArgument(denom.compareTo(BigInteger.ZERO) != 0);

		final var gcd = num.abs().gcd(denom.abs());
		if (denom.compareTo(BigInteger.ZERO) >= 0) {
			this.num = num.divide(gcd);
			this.denom = denom.divide(gcd);
		} else {
			this.num = num.divide(gcd).negate();
			this.denom = denom.divide(gcd).negate();
		}
	}

	public static RatLitExpr of(final BigInteger num, final BigInteger denom) {
		return new RatLitExpr(num, denom);
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public LitExpr<RatType> eval(final Valuation val) {
		return this;
	}

	public BigInteger getNum() {
		return num;
	}

	public BigInteger getDenom() {
		return denom;
	}

	public int sign() {
		return num.signum();
	}

	public BigInteger floor() {
		if (num.compareTo(BigInteger.ZERO) >= 0 || num.mod(denom).compareTo(BigInteger.ZERO) == 0) {
			return num.divide(denom);
		} else {
			return num.divide(denom).subtract(BigInteger.ONE);
		}
	}

	public BigInteger ceil() {
		if (num.compareTo(BigInteger.ZERO) <= 0 || num.mod(denom).compareTo(BigInteger.ZERO) == 0) {
			return num.divide(denom);
		} else {
			return num.divide(denom).add(BigInteger.ONE);
		}
	}

	public RatLitExpr add(final RatLitExpr that) {
		return RatLitExpr.of(this.getNum().multiply(that.getDenom()).add(this.getDenom().multiply(that.getNum())),
				this.getDenom().multiply(that.getDenom()));
	}

	public RatLitExpr sub(final RatLitExpr that) {
		return RatLitExpr.of(this.getNum().multiply(that.getDenom()).subtract(this.getDenom().multiply(that.getNum())),
				this.getDenom().multiply(that.getDenom()));
	}

	public RatLitExpr pos() {
		return RatLitExpr.of(this.getNum(), this.getDenom());
	}

	public RatLitExpr neg() {
		return RatLitExpr.of(this.getNum().negate(), this.getDenom());
	}

	public RatLitExpr mul(final RatLitExpr that) {
		return RatLitExpr.of(this.getNum().multiply(that.getNum()), this.getDenom().multiply(that.getDenom()));
	}

	public RatLitExpr div(final RatLitExpr that) {
		return RatLitExpr.of(this.getNum().multiply(that.getDenom()), this.getDenom().multiply(that.getNum()));
	}

	public BoolLitExpr eq(final RatLitExpr that) {
		return Bool(this.getNum().compareTo(that.getNum()) == 0 && this.getDenom().compareTo(that.getDenom()) == 0);
	}

	public BoolLitExpr neq(final RatLitExpr that) {
		return Bool(this.getNum().compareTo(that.getNum()) != 0 || this.getDenom().compareTo(that.getDenom()) != 0);
	}

	public BoolLitExpr lt(final RatLitExpr that) {
		return Bool(this.getNum().multiply(that.getDenom()).compareTo(this.getDenom().multiply(that.getNum())) < 0);
	}

	public BoolLitExpr leq(final RatLitExpr that) {
		return Bool(this.getNum().multiply(that.getDenom()).compareTo(this.getDenom().multiply(that.getNum())) <= 0);
	}

	public BoolLitExpr gt(final RatLitExpr that) {
		return Bool(this.getNum().multiply(that.getDenom()).compareTo(this.getDenom().multiply(that.getNum())) > 0);
	}

	public BoolLitExpr geq(final RatLitExpr that) {
		return Bool(this.getNum().multiply(that.getDenom()).compareTo(this.getDenom().multiply(that.getNum())) >= 0);
	}

	public RatLitExpr abs() {
		return RatLitExpr.of(num.abs(), denom);
	}

	public RatLitExpr frac() {
		return sub(of(floor(), BigInteger.ONE));
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + num.hashCode();
			result = 31 * result + denom.hashCode();
			hashCode = result;
		}
		return hashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatLitExpr) {
			final RatLitExpr that = (RatLitExpr) obj;
			return (this.getNum().compareTo(that.getNum()) == 0 && this.getDenom().compareTo(that.getDenom()) == 0);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getNum());
		sb.append('%');
		sb.append(getDenom());
		return sb.toString();
	}

	@Override
	public int compareTo(final RatLitExpr that) {
		return this.getNum().multiply(that.getDenom()).compareTo(this.getDenom().multiply(that.getNum()));
	}

}
