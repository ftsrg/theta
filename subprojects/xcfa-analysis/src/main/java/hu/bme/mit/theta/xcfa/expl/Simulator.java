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
package hu.bme.mit.theta.xcfa.expl;

import hu.bme.mit.theta.xcfa.XCFA;

/**
 * Checks for deadlock.
 * Checks that program ends on final location.
 * Assumes no livelock (it would get to an infinite loop)
 * Currently uninitialised variables only work for integers (and it assigns zero), sorry (due to ExplState)
 *
 * Uses a simple scheduler by default.
 */
public class Simulator {

	private final ExplState state;
	private final Scheduler s;

	public Simulator(XCFA xcfa) {
		s = enabledTransitions -> enabledTransitions.iterator().next();
		state = new ExplState(xcfa);
	}

	public Simulator(XCFA xcfa, Scheduler sched) {
		s = sched;
		state = new ExplState(xcfa);
	}

	public ExplState.StateSafety step() {
		state.step(s);
		return state.getSafety();
	}

}
