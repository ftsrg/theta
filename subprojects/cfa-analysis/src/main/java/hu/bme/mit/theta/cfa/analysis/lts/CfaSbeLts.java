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
package hu.bme.mit.theta.cfa.analysis.lts;

import java.util.Collection;
import java.util.stream.Collectors;

import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;

/**
 * Single block encoding (SBE) implementation for CFA LTS. It returns a single
 * CFA edges as actions.
 */
public final class CfaSbeLts implements CfaLts {

	private static final class LazyHolder {
		private static final CfaSbeLts INSTANCE = new CfaSbeLts();
	}

	private CfaSbeLts() {
	}

	public static CfaSbeLts getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public Collection<CfaAction> getEnabledActionsFor(final CfaState<?> state) {
		return state.getLoc().getOutEdges().stream().map(CfaAction::create).collect(Collectors.toList());
	}
}
