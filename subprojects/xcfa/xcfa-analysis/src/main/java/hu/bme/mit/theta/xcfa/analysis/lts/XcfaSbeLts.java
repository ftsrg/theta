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
package hu.bme.mit.theta.xcfa.analysis.lts;

import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Single block encoding (SBE) implementation for XCFA LTS. It returns a single
 * XCFA edges as actions.
 */
public final class XcfaSbeLts implements XcfaLts {

	private static final class LazyHolder {
		private static final XcfaSbeLts INSTANCE = new XcfaSbeLts();
	}

	private XcfaSbeLts() {
	}

	public static XcfaSbeLts getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public Collection<XcfaAction> getEnabledActionsFor(final XcfaState<?, ?, ?> state) {
		Collection<XcfaAction> ret = new ArrayList<>();
		for (Map.Entry<Integer, XcfaLocation> entry : state.getLocations().entrySet()) {
			Integer integer = entry.getKey();
			XcfaLocation xcfaLocation = entry.getValue();
			ret.addAll(xcfaLocation.getOutgoingEdges().stream().map(XcfaAction::create).collect(Collectors.toList()));
		}
		return ret;
	}
}
