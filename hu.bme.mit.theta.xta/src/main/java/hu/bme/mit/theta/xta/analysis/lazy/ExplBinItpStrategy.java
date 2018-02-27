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

import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.prod3.Prod3State;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.xta.analysis.zone.itp.ItpZoneState;

public final class ExplBinItpStrategy extends ExplItpStrategy {

	private ExplBinItpStrategy(final XtaSystem system) {
		super(system);
	}

	public static ExplBinItpStrategy create(final XtaSystem system) {
		return new ExplBinItpStrategy(system);
	}

	@Override
	protected ZoneState blockZone(
			final ArgNode<XtaState<Prod3State<ExplState, ExplState, ItpZoneState>>, XtaAction> node,
			final ZoneState zone,
			final Collection<ArgNode<XtaState<Prod3State<ExplState, ExplState, ItpZoneState>>, XtaAction>> uncoveredNodes,
			final LazyXtaStatistics.Builder stats) {

		final ZoneState abstrState = node.getState().getState().getState3().getAbstrState();
		if (abstrState.isConsistentWith(zone)) {
			stats.refineZone();

			final ZoneState concrState = node.getState().getState().getState3().getConcrState();
			final ZoneState interpolant = ZoneState.interpolant(concrState, zone);

			strengthenZone(node, interpolant);
			maintainZoneCoverage(node, interpolant, uncoveredNodes);

			if (node.getInEdge().isPresent()) {
				final ArgEdge<XtaState<Prod3State<ExplState, ExplState, ItpZoneState>>, XtaAction> inEdge = node
						.getInEdge().get();
				final XtaAction action = inEdge.getAction();
				final ArgNode<XtaState<Prod3State<ExplState, ExplState, ItpZoneState>>, XtaAction> parent = inEdge
						.getSource();
				final Collection<ZoneState> badZones = interpolant.complement();
				for (final ZoneState badZone : badZones) {
					final ZoneState preBadZone = pre(badZone, action);
					blockZone(parent, preBadZone, uncoveredNodes, stats);
				}
			}
			return interpolant;
		} else {
			return abstrState;
		}
	}

}
