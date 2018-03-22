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

import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;

public final class LazyXtaCheckerFactory {

	private LazyXtaCheckerFactory() {
	}

	public static SafetyChecker<? extends XtaState<?>, XtaAction, UnitPrec> create(final XtaSystem system,
			final DataStrategy dataStrategy, final ClockStrategy clockStrategy, final SearchStrategy searchStrategy) {
		final CombinedStrategy<?, ?> algorithmStrategy = combineStrategies(system, dataStrategy, clockStrategy);
		final SafetyChecker<? extends XtaState<?>, XtaAction, UnitPrec> checker = LazyXtaChecker.create(system,
				algorithmStrategy, searchStrategy);
		return checker;
	}

	private static CombinedStrategy<?, ?> combineStrategies(final XtaSystem system, final DataStrategy dataStrategy,
			final ClockStrategy clockStrategy) {

		switch (dataStrategy) {
		case BWITP:

			switch (clockStrategy) {
			case BWITP:
				return new CombinedStrategy<>(system, DataStrategies.createBwItpStrategy(system),
						ClockStrategies.createBwItpStrategy(system));
			case FWITP:
				return new CombinedStrategy<>(system, DataStrategies.createBwItpStrategy(system),
						ClockStrategies.createFwItpStrategy(system));
			case LU:
				return new CombinedStrategy<>(system, DataStrategies.createBwItpStrategy(system),
						ClockStrategies.createLuStrategy(system));
			default:
				throw new AssertionError();
			}

		case FWITP:

			switch (clockStrategy) {
			case BWITP:
				return new CombinedStrategy<>(system, DataStrategies.createFwItpStrategy(system),
						ClockStrategies.createBwItpStrategy(system));
			case FWITP:
				return new CombinedStrategy<>(system, DataStrategies.createFwItpStrategy(system),
						ClockStrategies.createFwItpStrategy(system));
			case LU:
				return new CombinedStrategy<>(system, DataStrategies.createFwItpStrategy(system),
						ClockStrategies.createLuStrategy(system));
			default:
				throw new AssertionError();
			}

		case NONE:

			switch (clockStrategy) {
			case BWITP:
				return new CombinedStrategy<>(system, DataStrategies.createExplStrategy(system),
						ClockStrategies.createBwItpStrategy(system));
			case FWITP:
				return new CombinedStrategy<>(system, DataStrategies.createExplStrategy(system),
						ClockStrategies.createFwItpStrategy(system));
			case LU:
				return new CombinedStrategy<>(system, DataStrategies.createExplStrategy(system),
						ClockStrategies.createLuStrategy(system));
			default:
				throw new AssertionError();
			}

		default:
			throw new AssertionError();
		}
	}
}
