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
package hu.bme.mit.theta.formalism.cfa.analysis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public class CfaLbeLts implements LTS<CfaState<?>, CfaAction> {

	private final Map<Loc, Collection<CfaAction>> actions;

	public CfaLbeLts() {
		actions = new HashMap<>();
	}

	@Override
	public Collection<CfaAction> getEnabledActionsFor(final CfaState<?> state) {
		return actions.computeIfAbsent(state.getLoc(), this::getEnabledActionsFor);
	}

	private Collection<CfaAction> getEnabledActionsFor(final Loc loc) {
		final List<CfaAction> actions = new ArrayList<>(loc.getOutEdges().size());

		for (final Edge edge : loc.getOutEdges()) {
			final Builder<Stmt> stmts = ImmutableList.builder();
			stmts.add(edge.getStmt());
			Loc running = edge.getTarget();
			while (running.getInEdges().size() == 1 && running.getOutEdges().size() == 1) {
				final Edge next = Utils.singleElementOf(running.getOutEdges());
				stmts.add(next.getStmt());
				running = next.getTarget();
			}
			actions.add(CfaAction.create(loc, running, stmts.build()));
		}

		return actions;
	}

}
