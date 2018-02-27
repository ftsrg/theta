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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;

final class ItpExplInitFunc implements InitFunc<ItpExplState, ExplPrec> {

	private final InitFunc<ExplState, ExplPrec> initFunc;

	private ItpExplInitFunc(final InitFunc<ExplState, ExplPrec> initFunc) {
		this.initFunc = checkNotNull(initFunc);
	}

	public static ItpExplInitFunc create(final InitFunc<ExplState, ExplPrec> initFunc) {
		return new ItpExplInitFunc(initFunc);
	}

	@Override
	public Collection<ItpExplState> getInitStates(final ExplPrec prec) {
		checkNotNull(prec);

		final Collection<? extends ExplState> subInitStates = initFunc.getInitStates(prec);

		if (subInitStates.isEmpty()) {
			final ItpExplState succState = ItpExplState.of(ExplState.bottom(), ExplState.top());
			return Collections.singleton(succState);
		} else {
			final Collection<ItpExplState> result = new ArrayList<>();
			for (final ExplState subInitState : subInitStates) {
				final ItpExplState initState = ItpExplState.of(subInitState, ExplState.top());
				result.add(initState);
			}
			return result;
		}
	}

}
