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
package hu.bme.mit.theta.core.type.proctype;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Type;

public final class ProcType<ReturnType extends Type> implements Type {

	private static final int HASH_SEED = 2069;
	private static final String TYPE_LABEL = "Proc";

	private final List<Type> paramTypes;
	private final ReturnType returnType;

	private volatile int hashCode = 0;

	ProcType(final Iterable<? extends Type> paramTypes, final ReturnType returnType) {
		this.paramTypes = ImmutableList.copyOf(checkNotNull(paramTypes));
		this.returnType = checkNotNull(returnType);
	}

	public List<Type> getParamTypes() {
		return paramTypes;
	}

	public ReturnType getReturnType() {
		return returnType;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + paramTypes.hashCode();
			result = 31 * result + returnType.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ProcType<?>) {
			final ProcType<?> that = (ProcType<?>) obj;
			return this.getParamTypes().equals(that.getParamTypes())
					&& this.getReturnType().equals(that.getReturnType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final String prefix = TYPE_LABEL + "(";
		sb.append(" -> ");
		sb.append(returnType.toString());
		sb.append(')');
		final String suffix = sb.toString();
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (final Type varType : paramTypes) {
			sj.add(varType.toString());
		}
		return sj.toString();
	}

}
