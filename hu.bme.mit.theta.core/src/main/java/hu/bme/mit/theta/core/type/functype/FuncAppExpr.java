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
package hu.bme.mit.theta.core.type.functype;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;

public final class FuncAppExpr<ParamType extends Type, ResultType extends Type> implements Expr<ResultType> {

	private static final int HASH_SEED = 7951;

	private static final String OPERATOR_LABEL = "app";

	private final Expr<FuncType<ParamType, ResultType>> func;
	private final Expr<ParamType> param;

	private volatile int hashCode = 0;

	FuncAppExpr(final Expr<FuncType<ParamType, ResultType>> func, final Expr<ParamType> param) {
		this.func = checkNotNull(func);
		this.param = checkNotNull(param);
	}

	public Expr<FuncType<ParamType, ResultType>> getFunc() {
		return func;
	}

	public Expr<ParamType> getParam() {
		return param;
	}

	@Override
	public ResultType getType() {
		return getFunc().getType().getResultType();
	}

	@Override
	public LitExpr<ResultType> eval(final Valuation val) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int getArity() {
		return 2;
	}

	@Override
	public List<Expr<?>> getOps() {
		return ImmutableList.of(func, param);
	}

	@Override
	public Expr<ResultType> withOps(final List<? extends Expr<?>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public FuncAppExpr<ParamType, ResultType> with(final Expr<FuncType<ParamType, ResultType>> func,
			final Expr<ParamType> param) {
		if (this.func == func && this.param == param) {
			return this;
		} else {
			return new FuncAppExpr<>(func, param);
		}
	}

	public FuncAppExpr<ParamType, ResultType> withFunc(final Expr<FuncType<ParamType, ResultType>> func) {
		return with(func, getParam());
	}

	public FuncAppExpr<ParamType, ResultType> withParam(final Expr<ParamType> param) {
		return with(getFunc(), param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + func.hashCode();
			result = 31 * result + param.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FuncAppExpr<?, ?>) {
			final FuncAppExpr<?, ?> that = (FuncAppExpr<?, ?>) obj;
			return this.getFunc().equals(that.getFunc()) && this.getParam().equals(that.getParam());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(OPERATOR_LABEL).add(func).add(param).toString();
	}

}
