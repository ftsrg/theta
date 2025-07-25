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
package hu.bme.mit.theta.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collections;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.rangetype.RangeType;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.IteratorDeclContext;

final class XtaIteratorSymbol implements Symbol {

	private final Scope scope;

	private final String name;
	private final XtaType xtaType;

	public XtaIteratorSymbol(final Scope scope, final IteratorDeclContext context) {
		this.scope = checkNotNull(scope);

		checkNotNull(context);
		name = context.fId.getText();
		xtaType = new XtaType(scope, context.fType, Collections.emptyList());
	}

	public VarDecl<RangeType> instantiate(final Env env) {
		final Optional<? extends Symbol> optSymbol = scope.resolve(name);
		if (optSymbol.isEmpty()) {
			throw new RuntimeException("Symbol \"" + name + "\" is undefined.");
		} else {
			final Symbol symbol = optSymbol.get();
			final Type type = xtaType.instantiate(env);
			if (type instanceof final RangeType rangeType) {
				final VarDecl<RangeType> varDecl = Decls.Var(name, rangeType);
				env.define(symbol, varDecl);
				return varDecl;
			} else {
				throw new UnsupportedOperationException("Type of iterator " + name + " is unsupported.");
			}
		}
	}

	@Override
	public String getName() {
		return name;
	}

}
