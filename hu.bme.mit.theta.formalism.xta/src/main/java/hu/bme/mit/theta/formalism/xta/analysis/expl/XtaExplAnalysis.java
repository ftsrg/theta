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

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;

public final class XtaExplAnalysis implements Analysis<ExplState, XtaAction, UnitPrec> {

	private final XtaExplInitFunc initFunc;
	private final XtaExplTransFunc transFunc;

	private XtaExplAnalysis(final XtaSystem system) {
		checkNotNull(system);
		initFunc = XtaExplInitFunc.create(system);
		transFunc = XtaExplTransFunc.create(system);
	}

	public static XtaExplAnalysis create(final XtaSystem system) {
		return new XtaExplAnalysis(system);
	}

	@Override
	public PartialOrd<ExplState> getPartialOrd() {
		return ExplOrd.getInstance();
	}

	@Override
	public InitFunc<ExplState, UnitPrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<ExplState, XtaAction, UnitPrec> getTransFunc() {
		return transFunc;
	}

}
