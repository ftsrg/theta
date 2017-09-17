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
package hu.bme.mit.theta.core.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decl;

public final class DeclSymbol implements Symbol {

	private static final int HASH_SEED = 8513;

	private volatile int hashCode = 0;

	private final Decl<?> decl;

	private DeclSymbol(final Decl<?> decl) {
		this.decl = checkNotNull(decl);
	}

	public static DeclSymbol of(final Decl<?> decl) {
		return new DeclSymbol(decl);
	}

	public Decl<?> getDecl() {
		return decl;
	}

	@Override
	public String getName() {
		return decl.getName();
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + decl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DeclSymbol) {
			final DeclSymbol that = (DeclSymbol) obj;
			return this.decl.equals(that.decl);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(getClass().getSimpleName()).add(decl).toString();
	}

}
