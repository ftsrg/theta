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

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Type;

public final class VarDecl<DeclType extends Type> extends AbstractDecl<DeclType> {
	private static final String DECL_LABEL = "Var";

	private final String name;
	private final DeclType type;
	private final Map<Integer, IndexedConstDecl<DeclType>> indexToConst;

	VarDecl(final String name, final DeclType type) {
		this.name = checkNotNull(name);
		this.type = checkNotNull(type);
		indexToConst = new HashMap<>();
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public DeclType getType() {
		return type;
	}

	public IndexedConstDecl<DeclType> getConstDecl(final int index) {
		checkArgument(index >= 0);
		IndexedConstDecl<DeclType> constDecl = indexToConst.get(index);
		if (constDecl == null) {
			constDecl = new IndexedConstDecl<>(this, index);
			indexToConst.put(index, constDecl);
		}
		return constDecl;
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(DECL_LABEL).add(name).add(type).toString();
	}

}
