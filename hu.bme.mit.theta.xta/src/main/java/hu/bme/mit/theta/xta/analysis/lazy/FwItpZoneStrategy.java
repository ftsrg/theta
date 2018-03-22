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

import java.util.Collection;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.xta.analysis.zone.itp.ItpZoneState;

final class FwItpZoneStrategy<S extends State> extends ItpZoneStrategy<S> {

	public FwItpZoneStrategy(final XtaSystem system, final Lens<S, ItpZoneState> lens) {
		super(system, lens);
	}

	@Override
	protected ZoneState blockZone(final ArgNode<S, XtaAction> node, final ZoneState zone,
			final Collection<ArgNode<S, XtaAction>> uncoveredNodes, final Builder stats) {
		final ZoneState abstrState = getLens().get(node.getState()).getAbstrState();
		if (abstrState.isConsistentWith(zone)) {
			stats.refineZone();
			if (node.getInEdge().isPresent()) {
				final ArgEdge<S, XtaAction> inEdge = node.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<S, XtaAction> parent = inEdge.getSource();

				final ZoneState B_pre = pre(zone, action);
				final ZoneState A_pre = blockZone(parent, B_pre, uncoveredNodes, stats);

				final ZoneState B = zone;
				final ZoneState A = post(A_pre, action);

				final ZoneState interpolant = ZoneState.interpolant(A, B);

				strengthen(node, interpolant);
				maintainCoverage(node, interpolant, uncoveredNodes);

				return interpolant;
			} else {
				final ZoneState concrState = getLens().get(node.getState()).getConcrState();

				final ZoneState interpolant = ZoneState.interpolant(concrState, zone);

				strengthen(node, interpolant);
				maintainCoverage(node, interpolant, uncoveredNodes);

				return interpolant;
			}
		} else {
			return abstrState;
		}
	}

}
