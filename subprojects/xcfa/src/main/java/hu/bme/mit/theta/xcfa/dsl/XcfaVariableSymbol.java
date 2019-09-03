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
package hu.bme.mit.theta.xcfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Var;

import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.VarDeclContext;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.VarDecl;

final class XcfaVariableSymbol implements Symbol {

	private final String name;
	private final XcfaType type;

	public XcfaVariableSymbol(final VarDeclContext context) {
		checkNotNull(context);
		name = context.ddecl.name.getText();
		type = new XcfaType(context.ddecl.ttype);
	}

	@Override
	public String getName() {
		return name;
	}

	public VarDecl<?> instantiate() {
		return Var(name, type.instantiate());
	}

}
