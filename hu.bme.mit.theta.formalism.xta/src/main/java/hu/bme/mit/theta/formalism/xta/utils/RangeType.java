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
package hu.bme.mit.theta.formalism.xta.utils;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;

public final class RangeType implements Type {
	private static final int HASH_SEED = 5441;
	private volatile int hashCode = 0;

	private final int lower;
	private final int upper;

	private RangeType(final int lower, final int upper) {
		checkArgument(lower <= upper);
		this.lower = lower;
		this.upper = upper;
	}

	public static RangeType Range(final int lower, final int upper) {
		return new RangeType(lower, upper);
	}

	public IntLitExpr Int(final int value) {
		checkArgument(value >= lower && value <= upper);
		return IntExprs.Int(value);
	}

	public Stream<IntLitExpr> values() {
		return IntStream.rangeClosed(lower, upper).mapToObj(IntExprs::Int);
	}

	public int getLower() {
		return lower;
	}

	public int getUpper() {
		return upper;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + lower;
			result = 31 * result + upper;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RangeType) {
			final RangeType that = (RangeType) obj;
			return this.lower == that.lower && this.upper == that.upper;
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder("Range").add(lower).add(upper).toString();
	}

}
