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

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Type;

public final class FuncType<ParamType extends Type, ResultType extends Type> implements Type {

	private final static int HASH_SEED = 3931;
	private final static String TYPE_LABEL = "Func";

	private final ParamType paramType;
	private final ResultType resultType;

	private volatile int hashCode = 0;

	private FuncType(final ParamType paramType, final ResultType resultType) {
		this.paramType = checkNotNull(paramType);
		this.resultType = checkNotNull(resultType);
	}

	public static <ParamType extends Type, ResultType extends Type> FuncType<ParamType, ResultType> of(
			final ParamType paramType, final ResultType resultType) {
		return new FuncType<>(paramType, resultType);
	}

	public ParamType getParamType() {
		return paramType;
	}

	public ResultType getResultType() {
		return resultType;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + paramType.hashCode();
			result = 31 * result + resultType.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FuncType<?, ?>) {
			final FuncType<?, ?> that = (FuncType<?, ?>) obj;
			return this.getParamType().equals(that.getParamType()) && this.getResultType().equals(that.getResultType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(TYPE_LABEL).add(paramType).add(resultType).toString();
	}

}
