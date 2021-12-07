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

public abstract class BinaryExpr<OpType extends Type, ExprType extends Type> implements Expr<ExprType> {

	private final Expr<OpType> leftOp;
	private final Expr<OpType> rightOp;

	private volatile int hashCode = 0;

	protected BinaryExpr(final Expr<OpType> leftOp, final Expr<OpType> rightOp) {
		this.leftOp = checkNotNull(leftOp);
		this.rightOp = checkNotNull(rightOp);
	}

	public final Expr<OpType> getLeftOp() {
		return leftOp;
	}

	public final Expr<OpType> getRightOp() {
		return rightOp;
	}

	@Override
	public final int getArity() {
		return 2;
	}

	@Override
	public final List<Expr<OpType>> getOps() {
		return ImmutableList.of(leftOp, rightOp);
	}

	@Override
	public final BinaryExpr<OpType, ExprType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 2);
		final OpType opType = getLeftOp().getType();
		final Expr<OpType> newLeftOp = TypeUtils.cast(ops.get(0), opType);
		final Expr<OpType> newRightOp = TypeUtils.cast(ops.get(1), opType);
		return with(newLeftOp, newRightOp);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + getLeftOp().hashCode();
			result = 31 * result + getRightOp().hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		return Utils.lispStringBuilder(getOperatorLabel()).add(leftOp).add(rightOp).toString();
	}

	public abstract BinaryExpr<OpType, ExprType> with(final Expr<OpType> leftOp, final Expr<OpType> rightOp);

	public abstract BinaryExpr<OpType, ExprType> withLeftOp(final Expr<OpType> leftOp);

	public abstract BinaryExpr<OpType, ExprType> withRightOp(final Expr<OpType> rightOp);

	protected abstract int getHashSeed();

	public abstract String getOperatorLabel();

}
