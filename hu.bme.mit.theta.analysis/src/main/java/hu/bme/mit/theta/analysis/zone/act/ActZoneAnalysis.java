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
package hu.bme.mit.theta.analysis.zone.act;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class ActZoneAnalysis<A extends Action> implements Analysis<ActZoneState, A, ZonePrec> {

	private final InitFunc<ActZoneState, ZonePrec> initFunc;
	private final TransFunc<ActZoneState, A, ZonePrec> transFunc;

	private ActZoneAnalysis(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		checkNotNull(analysis);
		initFunc = ActZoneInitFunc.create(analysis.getInitFunc());
		transFunc = ActZoneTransFunc.create(analysis.getTransFunc());
	}

	public static <A extends Action> ActZoneAnalysis<A> create(
			final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		return new ActZoneAnalysis<>(analysis);
	}

	@Override
	public PartialOrd<ActZoneState> getPartialOrd() {
		return ActZoneOrd.getInstance();
	}

	@Override
	public InitFunc<ActZoneState, ZonePrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<ActZoneState, A, ZonePrec> getTransFunc() {
		return transFunc;
	}

}
