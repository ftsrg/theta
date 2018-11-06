/*
 *  Copyright 2018 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.expl.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;

public final class ItpExplAnalysis<A extends Action> implements Analysis<ItpExplState, A, UnitPrec> {

	private final InitFunc<ItpExplState, UnitPrec> initFunc;
	private final TransFunc<ItpExplState, A, UnitPrec> transFunc;

	private ItpExplAnalysis(final Analysis<ExplState, ? super A, UnitPrec> analysis) {
		checkNotNull(analysis);
		initFunc = ItpExplInitFunc.create(analysis.getInitFunc());
		transFunc = ItpExplTransFunc.create(analysis.getTransFunc());
	}

	public static <A extends Action> ItpExplAnalysis<A> create(
			final Analysis<ExplState, ? super A, UnitPrec> analysis) {
		return new ItpExplAnalysis<>(analysis);
	}

	@Override
	public PartialOrd<ItpExplState> getPartialOrd() {
		return ItpExplOrd.getInstance();
	}

	@Override
	public InitFunc<ItpExplState, UnitPrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<ItpExplState, A, UnitPrec> getTransFunc() {
		return transFunc;
	}

}
