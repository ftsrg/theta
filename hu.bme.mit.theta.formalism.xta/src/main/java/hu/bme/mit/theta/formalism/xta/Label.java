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
package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Type;

public final class Label {

	private static final int HASH_SEED = 8527;
	private volatile int hashCode = 0;

	private final String name;
	private final List<Type> paramTypes;

	private Label(final String name, final List<? extends Type> paramTypes) {
		this.name = checkNotNull(name);
		this.paramTypes = ImmutableList.copyOf(checkNotNull(paramTypes));
	}

	public static Label of(final String name, final List<? extends Type> paramTypes) {
		return new Label(name, paramTypes);
	}

	public String getName() {
		return name;
	}

	public List<Type> getParamTypes() {
		return paramTypes;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + name.hashCode();
			result = 31 * result + paramTypes.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return super.equals(obj);
	}

	@Override
	public String toString() {
		return name;
	}

}
