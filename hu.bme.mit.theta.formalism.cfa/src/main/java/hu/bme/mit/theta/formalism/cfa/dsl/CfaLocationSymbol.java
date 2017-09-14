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
package hu.bme.mit.theta.formalism.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.LocContext;

final class CfaLocationSymbol implements Symbol {

	private final boolean init;
	private final boolean finall;
	private final boolean error;
	private final String name;

	public CfaLocationSymbol(final LocContext context) {
		checkNotNull(context);
		init = (context.init != null);
		finall = (context.finall != null);
		error = (context.error != null);
		name = context.id.getText();
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isInit() {
		return init;
	}

	public boolean isFinal() {
		return finall;
	}

	public boolean isError() {
		return error;
	}

	public Loc intantiate(final CFA.Builder cfaBuilder) {
		final Loc loc = cfaBuilder.createLoc(name);

		if (init) {
			cfaBuilder.setInitLoc(loc);
		} else if (finall) {
			cfaBuilder.setFinalLoc(loc);
		} else if (error) {
			cfaBuilder.setErrorLoc(loc);
		}

		return loc;
	}

}
