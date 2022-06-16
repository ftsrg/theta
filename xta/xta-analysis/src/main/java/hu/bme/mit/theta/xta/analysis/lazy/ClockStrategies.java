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
package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneState;

final class ClockStrategies {

	private ClockStrategies() {
	}

	public static <S extends State> AlgorithmStrategy<XtaState<Prod2State<S, LuZoneState>>, LuZoneState> createLuStrategy(
			final XtaSystem system) {
		return new LuZoneStrategy<>(system, createRightLens());
	}

	public static <S extends State> AlgorithmStrategy<XtaState<Prod2State<S, ItpZoneState>>, ItpZoneState> createFwItpStrategy(
			final XtaSystem system) {
		return new FwItpZoneStrategy<>(system, createRightLens());
	}

	public static <S extends State> AlgorithmStrategy<XtaState<Prod2State<S, ItpZoneState>>, ItpZoneState> createBwItpStrategy(
			final XtaSystem system) {
		return new BwItpZoneStrategy<>(system, createRightLens());
	}

	private static <S1 extends State, S2 extends State> Lens<XtaState<Prod2State<S1, S2>>, S2> createRightLens() {
		return new Lens<XtaState<Prod2State<S1, S2>>, S2>() {
			@Override
			public S2 get(final XtaState<Prod2State<S1, S2>> state) {
				return state.getState().getState2();
			}

			@Override
			public XtaState<Prod2State<S1, S2>> set(final XtaState<Prod2State<S1, S2>> state, final S2 s2) {
				final Prod2State<S1, S2> prodState = state.getState();
				final Prod2State<S1, S2> newProdState = prodState.with2(s2);
				final XtaState<Prod2State<S1, S2>> newState = state.withState(newProdState);
				return newState;
			}
		};
	}

}
