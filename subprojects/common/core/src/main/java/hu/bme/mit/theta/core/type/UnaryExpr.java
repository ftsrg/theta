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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.utils.TypeUtils;

public abstract class UnaryExpr<OpType extends Type, ExprType extends Type> implements Expr<ExprType> {

	private final Expr<OpType> op;

	private volatile int hashCode = 0;

	public UnaryExpr(final Expr<OpType> op) {
		this.op = checkNotNull(op);
	}

	public final Expr<OpType> getOp() {
		return op;
	}

	@Override
	public final List<Expr<OpType>> getOps() {
		return ImmutableList.of(op);
	}

	@Override
	public final UnaryExpr<OpType, ExprType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 1);
		final OpType opType = op.getType();
		final Expr<OpType> newOp = TypeUtils.cast(ops.get(0), opType);
		return with(newOp);
	}

	@Override
	public int getArity() {
		return 1;
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 37 * result + getOp().hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public final String toString() {
		return Utils.lispStringBuilder(getOperatorLabel()).add(op).toString();
	}

	public abstract UnaryExpr<OpType, ExprType> with(final Expr<OpType> op);

	protected abstract int getHashSeed();

	public abstract String getOperatorLabel();
}
