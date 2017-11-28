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
package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class WpState {
	private static final int HASH_SEED = 2029;
	private volatile int hashCode = 0;

	private final Expr<BoolType> expr;
	private final int constCount;

	private WpState(final Expr<BoolType> expr, final int constCount) {
		checkNotNull(expr);
		checkArgument(constCount >= 0);
		this.expr = expr;
		this.constCount = constCount;
	}

	public static WpState of(final Expr<BoolType> expr, final int constCount) {
		return new WpState(expr, constCount);
	}

	public Expr<BoolType> getExpr() {
		return expr;
	}

	public int getConstCount() {
		return constCount;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + expr.hashCode();
			result = 31 * result + constCount;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof WpState) {
			final WpState that = (WpState) obj;
			return this.constCount == that.constCount && this.expr.equals(that.expr);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).add(expr).add(Integer.valueOf(constCount))
				.toString();
	}
}
