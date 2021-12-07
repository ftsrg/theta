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

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import hu.bme.mit.theta.cfa.CFA.Edge;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;
import hu.bme.mit.theta.common.Utils;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Large block encoding (LBE) implementation for CFA LTS. It maps each path
 * (with no branching) into a single action.
 */
public final class CfaLbeLts implements CfaLts {

	private final Loc targetLoc;

	private CfaLbeLts(Loc targetLoc) {
		this.targetLoc = checkNotNull(targetLoc, "Target location must be given for LBE encoder.");
	}

	public static CfaLbeLts of(Loc targetLoc) {
		return new CfaLbeLts(targetLoc);
	}

	@Override
	public Collection<CfaAction> getEnabledActionsFor(final CfaState<?> state) {
		final Loc loc = state.getLoc();
		final List<CfaAction> actions = new ArrayList<>(loc.getOutEdges().size());

		for (final Edge edge : loc.getOutEdges()) {
			final List<Edge> edges = new LinkedList<>();
			edges.add(edge);
			Loc running = edge.getTarget();
			while (running.getInEdges().size() == 1 && running.getOutEdges().size() == 1 && !running.equals(targetLoc)) {
				final Edge next = Utils.singleElementOf(running.getOutEdges());
				edges.add(next);
				running = next.getTarget();
			}
			actions.add(CfaAction.create(edges));
		}

		return actions;
	}

}
