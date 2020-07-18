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

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Type;

/**
 * Abstract base class for constants. Use {@link BasicConstDecl} for a basic
 * constant, or {@link IndexedConstDecl} if the constant belongs to a variable
 * for some index (e.g., during unfolding paths).
 * @param <DeclType>
 */
public abstract class ConstDecl<DeclType extends Type> extends Decl<DeclType> {
	private static final String DECL_LABEL = "Const";

	ConstDecl(final String name, final DeclType type) {
		super(name, type);
	}

	@Override
	public final String toString() {
		return Utils.lispStringBuilder(DECL_LABEL).add(getName()).add(getType()).toString();
	}

}
