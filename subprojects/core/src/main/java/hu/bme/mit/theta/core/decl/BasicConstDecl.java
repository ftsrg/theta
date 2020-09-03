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

import hu.bme.mit.theta.core.type.Type;

/**
 * A basic constant declaration that can be directly passed to the SMT solver.
 * @param <DeclType>
 */
public final class BasicConstDecl<DeclType extends Type> extends ConstDecl<DeclType> {

	BasicConstDecl(final String name, final DeclType type) {
		super(name, type);
	}

}
