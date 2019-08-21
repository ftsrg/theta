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
package hu.bme.mit.theta.xta.analysis;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xta.Label;
import hu.bme.mit.theta.xta.Sync;
import hu.bme.mit.theta.xta.Sync.Kind;
import hu.bme.mit.theta.xta.XtaProcess.Edge;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.XtaSystem;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;
import static hu.bme.mit.theta.xta.Sync.Kind.EMIT;
import static hu.bme.mit.theta.xta.XtaProcess.LocKind.COMMITTED;
import static java.util.stream.Collectors.toList;

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
		if (edge.getSync().isPresent()) {
			final Sync sync = edge.getSync().get();
			if (sync.getKind() == EMIT) {
				if (sync.getLabel().isBroadcast()) {
					addBroadcastActionsForEdge(result, system, state, edge, sync);
				} else {
					addBinaryActionsForEdge(result, system, state, edge, sync);
				}
			}
		} else {
			addBasicActionsForEdge(result, system, state, edge);
		}
	}

	private static void addBroadcastActionsForEdge(final Collection<XtaAction> result, final XtaSystem system,
												   final XtaState<?> state, final Edge emitEdge, final Sync emitSync) {
		assert emitEdge.getSync().isPresent();
		assert emitEdge.getSync().get().equals(emitSync);
		assert emitSync.getKind().equals(EMIT);
		assert emitSync.getLabel().isBroadcast();

		final Collection<List<Edge>> initialRecvEdgeColls = new ArrayList<>();
		initialRecvEdgeColls.add(new ArrayList<>());
		Collection<List<Edge>> recvEdgeColls = recvEdgesForEmitEdge(emitEdge, emitSync, state.getLocs(), initialRecvEdgeColls);

		// filter out all non well-formed actions if the state is committed
		final Loc emitLoc = emitEdge.getSource();
		if (state.isCommitted() && emitLoc.getKind() != COMMITTED) {
			recvEdgeColls = recvEdgeColls.stream().filter(edges ->
					edges.stream().anyMatch(edge ->
							edge.getSource().getKind() == COMMITTED)).collect(toList());
		}

		for (List<Edge> recvEdges : recvEdgeColls) {
			result.add(XtaAction.broadcast(system, state.getLocs(), emitEdge, recvEdges));
		}
	}

	private static Collection<List<Edge>> recvEdgesForEmitEdge(final Edge emitEdge, final Sync emitSync,
															   final List<Loc> remainingLocs,
															   final Collection<List<Edge>> accumulator) {
		assert emitEdge.getSync().isPresent();
		assert emitEdge.getSync().get().equals(emitSync);
		assert emitSync.getKind().equals(EMIT);
		assert emitSync.getLabel().isBroadcast();

		if (remainingLocs.isEmpty()) {
			return accumulator;

		} else {
			final Loc emitLoc = emitEdge.getSource();
			final Loc recvLoc = head(remainingLocs);
			final List<Loc> newRemainingLocs = tail(remainingLocs);

			final Collection<List<Edge>> newAccumulator;

			if (emitLoc.equals(recvLoc)) {
				newAccumulator = accumulator;

			} else {
				newAccumulator = new ArrayList<>();

				for (List<Edge> recvEdges : accumulator) {
					// add all receiving edges to the result set
					for (Edge recvEdge : recvLoc.getOutEdges()) {
						if (recvEdge.getSync().isPresent()) {
							final Sync recvSync = recvEdge.getSync().get();
							if (recvSync.mayReceive(emitSync)) {
								final List<Edge> newRecvEdges = new ArrayList<>(recvEdges);
								newRecvEdges.add(recvEdge);
								newAccumulator.add(newRecvEdges);
							}
						}
					}

					// include the case when none of the syncronizing edges can fire
					newAccumulator.add(recvEdges);
				}
			}

			return recvEdgesForEmitEdge(emitEdge, emitSync, newRemainingLocs, newAccumulator);
		}
	}


	private static void addBinaryActionsForEdge(final Collection<XtaAction> result, final XtaSystem system,
												final XtaState<?> state, final Edge emitEdge, final Sync emitSync) {
		assert emitEdge.getSync().isPresent();
		assert emitEdge.getSync().get().equals(emitSync);
		assert emitSync.getKind().equals(EMIT);
		assert !emitSync.getLabel().isBroadcast();

		final Loc emitLoc = emitEdge.getSource();
		final Label emitLabel = emitSync.getLabel();

		for (final Loc recvLoc : state.getLocs()) {
			if (recvLoc == emitLoc) {
				continue;
			}

			if (state.isCommitted() && emitLoc.getKind() != COMMITTED && recvLoc.getKind() != COMMITTED) {
				continue;
			}

			for (final Edge recvEdge : recvLoc.getOutEdges()) {
				if (!recvEdge.getSync().isPresent()) {
					continue;
				}

				final Sync recvSync = recvEdge.getSync().get();
				if (recvSync.getKind() != Kind.RECV) {
					continue;
				}

				final Label recvLabel = recvSync.getLabel();

				if (emitLabel.equals(recvLabel)) {
					final XtaAction action = XtaAction.binary(system, state.getLocs(), emitEdge, recvEdge);
					result.add(action);
				}
			}
		}
	}

	private static void addBasicActionsForEdge(final Collection<XtaAction> result, final XtaSystem system,
											   final XtaState<?> state, final Edge edge) {
		final Loc loc = edge.getSource();
		if (state.isCommitted() && loc.getKind() != COMMITTED) {
			return;
		}
		final XtaAction action = XtaAction.basic(system, state.getLocs(), edge);
		result.add(action);
	}

}
