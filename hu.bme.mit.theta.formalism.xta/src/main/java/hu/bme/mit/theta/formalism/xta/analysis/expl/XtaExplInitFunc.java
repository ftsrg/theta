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
package hu.bme.mit.theta.formalism.xta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static java.util.Collections.singleton;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.BasicValuation;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

final class XtaExplInitFunc implements InitFunc<ExplState, UnitPrec> {

	private final Collection<VarDecl<?>> vars;

	private XtaExplInitFunc(final XtaSystem system) {
		checkNotNull(system);
		vars = system.getDataVars();
	}

	public static XtaExplInitFunc create(final XtaSystem system) {
		return new XtaExplInitFunc(system);
	}

	@Override
	public Collection<ExplState> getInitStates(final UnitPrec prec) {
		checkNotNull(prec);
		final BasicValuation.Builder builder = BasicValuation.builder();
		for (final VarDecl<?> var : vars) {
			final Type type = var.getType();
			if (type instanceof BoolType) {
				builder.put(var, False());
			} else if (type instanceof IntType) {
				builder.put(var, Int(0));
			} else {
				throw new UnsupportedOperationException();
			}
		}
		final BasicValuation val = builder.build();
		final ExplState initState = ExplState.create(val);
		return singleton(initState);
	}

}
