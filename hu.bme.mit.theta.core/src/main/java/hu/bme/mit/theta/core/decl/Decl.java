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
package hu.bme.mit.theta.core.decl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ref;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

public abstract class Decl<DeclType extends Type> {
	private static final int HASH_SEED = 5351;
	private volatile int hashCode = 0;

	private final String name;
	private final DeclType type;
	private final RefExpr<DeclType> ref;

	public Decl(final String name, final DeclType type) {
		checkNotNull(name);
		checkArgument(name.length() > 0);
		this.name = name;
		this.type = checkNotNull(type);
		this.ref = Ref(this);
	}

	public final String getName() {
		return name;
	}

	public final DeclType getType() {
		return type;
	}

	public final RefExpr<DeclType> getRef() {
		return ref;
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + getName().hashCode();
			result = 31 * result + getType().hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		return this == obj;
	}

}
