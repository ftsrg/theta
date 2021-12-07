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
package hu.bme.mit.theta.core.type.anytype;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class IteExpr<ExprType extends Type> implements Expr<ExprType> {

	private static final int HASH_SEED = 181;
	private static final String OPERATOR_LABEL = "ite";

	private final Expr<BoolType> cond;
	private final Expr<ExprType> then;
	private final Expr<ExprType> elze;

	private volatile int hashCode = 0;

	private IteExpr(final Expr<BoolType> cond, final Expr<ExprType> then, final Expr<ExprType> elze) {
		this.cond = checkNotNull(cond);
		this.then = checkNotNull(then);
		this.elze = checkNotNull(elze);
	}

	public static <ExprType extends Type> IteExpr<ExprType> of(final Expr<BoolType> cond, final Expr<ExprType> then,
															   final Expr<ExprType> elze) {
		return new IteExpr<>(cond, then, elze);
	}

	public static <ExprType extends Type> IteExpr<?> create(final Expr<?> cond, final Expr<?> then, final Expr<?> elze) {
		final Expr<BoolType> newCond = cast(cond, Bool());
		@SuppressWarnings("unchecked") final Expr<ExprType> newThen = (Expr<ExprType>) then;
		final Expr<ExprType> newElze = cast(elze, newThen.getType());
		return IteExpr.of(newCond, newThen, newElze);
	}

	public Expr<BoolType> getCond() {
		return cond;
	}

	public Expr<ExprType> getThen() {
		return then;
	}

	public Expr<ExprType> getElse() {
		return elze;
	}

	@Override
	public List<Expr<?>> getOps() {
		return ImmutableList.of(cond, then, elze);
	}

	@Override
	public int getArity() {
		return 3;
	}

	@Override
	public ExprType getType() {
		return getThen().getType();
	}

	@Override
	public LitExpr<ExprType> eval(final Valuation val) {
		final BoolLitExpr condVal = (BoolLitExpr) cond.eval(val);
		if (condVal.getValue()) {
			return then.eval(val);
		} else {
			return elze.eval(val);
		}
	}

	@Override
	public IteExpr<ExprType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 3);
		final ExprType exprType = getType();
		final Expr<BoolType> newCond = cast(ops.get(0), Bool());
		final Expr<ExprType> newThen = cast(ops.get(1), exprType);
		final Expr<ExprType> newElze = cast(ops.get(2), exprType);
		return with(newCond, newThen, newElze);
	}

	public IteExpr<ExprType> with(final Expr<BoolType> cond, final Expr<ExprType> then, final Expr<ExprType> elze) {
		if (this.cond == cond && this.then == then && this.elze == elze) {
			return this;
		} else {
			return IteExpr.of(cond, then, elze);
		}
	}

	public IteExpr<ExprType> withCond(final Expr<BoolType> cond) {
		return with(cond, getThen(), getElse());
	}

	public IteExpr<ExprType> withThen(final Expr<ExprType> then) {
		return with(getCond(), then, getElse());
	}

	public IteExpr<ExprType> withElse(final Expr<ExprType> elze) {
		return with(getCond(), getThen(), elze);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + cond.hashCode();
			result = 31 * result + then.hashCode();
			result = 31 * result + elze.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IteExpr) {
			final IteExpr<?> that = (IteExpr<?>) obj;
			return this.getCond().equals(that.getCond()) && this.getThen().equals(that.getThen())
					&& this.getElse().equals(that.getElse());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(OPERATOR_LABEL).add(getCond()).add(getThen()).add(getElse()).toString();
	}

}
