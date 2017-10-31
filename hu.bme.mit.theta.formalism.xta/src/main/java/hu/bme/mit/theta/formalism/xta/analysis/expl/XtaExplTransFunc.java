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

import java.util.Collection;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.solver.impl.NullSolver;

final class XtaExplTransFunc implements TransFunc<ExplState, XtaAction, UnitPrec> {

	private final ExplPrec explPrec;
	private final ExplStmtTransFunc transFunc;

	private XtaExplTransFunc(final XtaSystem system) {
		checkNotNull(system);
		explPrec = ExplPrec.of(system.getDataVars());
		transFunc = ExplStmtTransFunc.create(NullSolver.getInstance(), 0);
	}

	public static XtaExplTransFunc create(final XtaSystem system) {
		return new XtaExplTransFunc(system);
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final XtaAction action, final UnitPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		return transFunc.getSuccStates(state, action, explPrec);
	}

}
