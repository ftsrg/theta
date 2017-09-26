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
package hu.bme.mit.theta.formalism.xta.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.xta.ChanType;
import hu.bme.mit.theta.formalism.xta.Label;
import hu.bme.mit.theta.formalism.xta.Label.Kind;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaLts implements LTS<XtaState<?>, XtaAction> {

	private final XtaSystem system;

	private XtaLts(final XtaSystem system) {
		this.system = checkNotNull(system);
	}

	public static XtaLts create(final XtaSystem system) {
		return new XtaLts(system);
	}

	@Override
	public Collection<XtaAction> getEnabledActionsFor(final XtaState<?> state) {
		final Collection<XtaAction> result = new ArrayList<>();
		for (final Loc loc : state.getLocs()) {
			for (final Edge edge : loc.getOutEdges()) {
				addActionsForEdge(result, system, state, edge);
			}
		}
		return result;
	}

	private static void addActionsForEdge(final Collection<XtaAction> result, final XtaSystem system,
			final XtaState<?> state, final Edge edge) {
		if (edge.getLabel().isPresent()) {
			addSyncActionsForEdge(result, system, state, edge);
		} else {
			addSimpleActionsForEdge(result, system, state, edge);
		}
	}

	private static void addSyncActionsForEdge(final Collection<XtaAction> result, final XtaSystem system,
			final XtaState<?> state, final Edge emitEdge) {

		final Loc emitLoc = emitEdge.getSource();
		final Label emitLabel = emitEdge.getLabel().get();
		if (emitLabel.getKind() != Kind.EMIT) {
			return;
		}

		final Expr<ChanType> emitExpr = ExprUtils.simplify(emitLabel.getExpr(), state.getVal());

		for (final Loc receiveLoc : state.getLocs()) {
			if (receiveLoc == emitLoc) {
				continue;
			}

			for (final Edge recieveEdge : receiveLoc.getOutEdges()) {
				if (!recieveEdge.getLabel().isPresent()) {
					continue;
				}

				final Label receiveLabel = recieveEdge.getLabel().get();
				if (receiveLabel.getKind() != Kind.RECEIVE) {
					continue;
				}

				final Expr<?> receiveExpr = ExprUtils.simplify(receiveLabel.getExpr(), state.getVal());
				if (emitExpr.equals(receiveExpr)) {
					final XtaAction action = XtaAction.synced(system, state.getLocs(), emitExpr, emitEdge, recieveEdge);
					result.add(action);
				}
			}
		}
	}

	private static void addSimpleActionsForEdge(final Collection<XtaAction> result, final XtaSystem system,
			final XtaState<?> state, final Edge edge) {
		final XtaAction action = XtaAction.simple(system, state.getLocs(), edge);
		result.add(action);
	}

}
