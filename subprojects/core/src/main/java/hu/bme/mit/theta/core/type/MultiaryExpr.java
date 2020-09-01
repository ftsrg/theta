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
package hu.bme.mit.theta.core.type;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.utils.TypeUtils;

public abstract class MultiaryExpr<OpType extends Type, ExprType extends Type> implements Expr<ExprType> {

	private final List<Expr<OpType>> ops;

	private volatile int hashCode = 0;

	protected MultiaryExpr(final Iterable<? extends Expr<OpType>> ops) {
		checkNotNull(ops);
		this.ops = ImmutableList.copyOf(ops);
	}

	@Override
	public final int getArity() {
		return ops.size();
	}

	@Override
	public final List<Expr<OpType>> getOps() {
		return ops;
	}

	@Override
	public final MultiaryExpr<OpType, ExprType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		if (ops.isEmpty()) {
			return with(ImmutableList.of());
		} else {
			final OpType opType = getOps().get(0).getType();
			final List<Expr<OpType>> newOps = ops.stream().map(op -> TypeUtils.cast(op, opType))
					.collect(toImmutableList());
			return with(newOps);
		}
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + getOps().hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		return Utils.lispStringBuilder(getOperatorLabel()).addAll(ops).toString();
	}

	public abstract MultiaryExpr<OpType, ExprType> with(final Iterable<? extends Expr<OpType>> ops);

	protected abstract int getHashSeed();

	public abstract String getOperatorLabel();

}
