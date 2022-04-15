/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.*;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.function.Predicate;

public final class XcfaLts implements LTS<XcfaState<?>, XcfaAction> {

	public enum POR_MODE {
		POR_OFF, POR_ON
	}

	public static POR_MODE porMode = POR_MODE.POR_ON;

	private GlobalVarQuery globalVarQuery = null;

	/**
	 * Returns the enabled actions in the ARG from the given state.
	 *
	 * @param state the state whose enabled actions we would like to know
	 * @return the enabled actions
	 */
	@Override
	public Collection<XcfaAction> getEnabledActionsFor(final XcfaState<?> state) {
		final List<XcfaAction> xcfaActions = new ArrayList<>();
		switch (porMode) {
			case POR_OFF: // Every outgoing edge of every enabled process is returned
				for (Integer enabledProcess : state.getEnabledProcesses()) {
					final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
					for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
						final XcfaAction xcfaAction = XcfaAction.create(enabledProcess, outgoingEdge);
						xcfaActions.add(xcfaAction);
					}
				}
				break;

			case POR_ON: // Only the elements of a minimal (minimal with our algorithm) persistent set is returned

				// Collecting enabled edges (with their processes)
				List<SimpleImmutableEntry<XcfaEdge, Integer>> enabledEdges = new ArrayList<>();
				for (Integer enabledProcess : state.getEnabledProcesses()) {
					final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
					for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
						enabledEdges.add(new SimpleImmutableEntry<>(outgoingEdge, enabledProcess));
					}
				}

				// Initializing the global variable query manager and the XCFA backward edge registry
				if (globalVarQuery == null && enabledEdges.size() > 0) {
					XCFA xcfa = enabledEdges.get(0).getKey().getSource().getParent().getParent().getParent();
					globalVarQuery = new GlobalVarQuery(xcfa);
					collectBackwardEdges(xcfa);
				}

				// Calculating the persistent set starting from every enabled edge; the minimal persistent set is stored
				Set<SimpleImmutableEntry<XcfaEdge, Integer>> minimalPersistentSet = null;
				for (Integer enabledProcess : state.getEnabledProcesses()) {
					final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
					if(loc.getOutgoingEdges().size() == 0) continue;

					var startingEdge = new SimpleImmutableEntry<>(loc.getOutgoingEdges().get(0), enabledProcess);
					Set<SimpleImmutableEntry<XcfaEdge, Integer>> persistentSet = calculatePersistentSet(enabledEdges, startingEdge);
					if (minimalPersistentSet == null || persistentSet.size() < minimalPersistentSet.size()) {
						minimalPersistentSet = persistentSet;
					}
				}

				// Convert persistent set to action list
				if (minimalPersistentSet != null) {
					for (var edge : minimalPersistentSet) {
						final XcfaAction xcfaAction = XcfaAction.create(edge.getValue(), edge.getKey());
						xcfaActions.add(xcfaAction);
					}
				}

				break;
		}
		return xcfaActions;
	}


	/**
	 * Calculates the persistent set starting from the specified edge.
	 * An edge is added to the persistent set if any of the two following conditions are met:
	 * - an edge of the same process is already in the persistent set
	 * - uses a global variable (or an edge reachable via this edge uses a global variable) that is used by an edge in
	 * the set
	 *
	 * @param enabledEdges The enabled transitions (edges) that can be taken at the present state.
	 * @param startingEdge The edge that is the first element of the persistent set.
	 * @return Returns the calculated persistent set: a set of edges (and their processes).
	 */
	private Set<SimpleImmutableEntry<XcfaEdge, Integer>> calculatePersistentSet(List<SimpleImmutableEntry<XcfaEdge, Integer>> enabledEdges, SimpleImmutableEntry<XcfaEdge, Integer> startingEdge) {
		if (backwardEdges.contains(startingEdge.getKey())) return new HashSet<>(enabledEdges);

		Set<SimpleImmutableEntry<XcfaEdge, Integer>> persistentSet = new HashSet<>();
		Set<Integer> processesInPS = new HashSet<>(); // the id number of the processes who has at least one edge already in the persistent set
		Set<VarDecl<? extends Type>> globalVarsInPS = new HashSet<>(); // the used or influenced global variables that are used by at least on edge already in the persistent set
		List<SimpleImmutableEntry<XcfaEdge, Integer>> otherEdges = new ArrayList<>(enabledEdges); // edges not in the persistent set

		persistentSet.add(startingEdge);
		processesInPS.add(startingEdge.getValue());
		globalVarsInPS.addAll(globalVarQuery.getUsedGlobalVars(startingEdge.getKey()));
		otherEdges.remove(startingEdge);

		boolean addedNewEdge = true;
		while (addedNewEdge) {
			addedNewEdge = false;
			for (int i = 0; i < otherEdges.size(); i++) {
				// for every edge that is not in the persistent set it is checked whether it should be added to the persistent set
				// (either because an edge in the same process is already in the persistent set or uses a global variable that is also used by an edge in the persistent set)
				SimpleImmutableEntry<XcfaEdge, Integer> action = otherEdges.get(i);
				XcfaEdge edge = action.getKey();
				Integer process = action.getValue();

				if (processesInPS.contains(process) || globalVarQuery.getInfluencedGlobalVars(edge).stream().anyMatch(globalVarsInPS::contains)) {
					if (backwardEdges.contains(edge)) {
						return new HashSet<>(enabledEdges); // to prevent ignoring other threads in "infinite" loops, at least once in every loop (at a backward edge) all enabled edges are returned
					}

					persistentSet.add(action);
					processesInPS.add(process);
					globalVarsInPS.addAll(globalVarQuery.getUsedGlobalVars(edge));
					otherEdges.remove(action);
					i--;
					addedNewEdge = true;
				}
			}
		}

		return persistentSet;
	}


	/**
	 * Provides different methods for querying certain global variables.
	 */
	private static class GlobalVarQuery {
		/**
		 * Global variables in the XCFA.
		 */
		private final List<VarDecl<? extends Type>> globalVars;

		/**
		 * Global variables used by an edge.
		 */
		private final HashMap<XcfaEdge, Set<VarDecl<? extends Type>>> usedGlobalVars = new HashMap<>();

		/**
		 * Global variables that are used by the key edge or by edges reachable from the current state via a given edge.
		 */
		private final HashMap<XcfaEdge, Set<VarDecl<? extends Type>>> influencedGlobalVars = new HashMap<>();

		GlobalVarQuery(XCFA xcfa) {
			globalVars = xcfa.getGlobalVars();
		}

		/**
		 * Returns the global variables that an edge uses (it is present in one of its labels).
		 *
		 * @param edge whose global variables are to be returned
		 * @return the set of used global variables
		 */
		private Set<VarDecl<? extends Type>> getDirectlyUsedGlobalVars(XcfaEdge edge) {
			Set<VarDecl<?>> vars = new HashSet<>();
			edge.getLabels().forEach(label -> LabelUtils.getVars(label).forEach(usedVar -> {
				if (globalVars.contains(usedVar)) {
					vars.add(usedVar);
				}
			}));
			return vars;
		}

		/**
		 * Returns the global variables that an edge uses or if it is the start of an atomic block the global variables
		 * that are used in the atomic block.
		 *
		 * @param edge whose global variables are to be returned
		 * @return the set of directly or indirectly used global variables
		 */
		private Set<VarDecl<? extends Type>> getUsedGlobalVars(XcfaEdge edge) {
			if (!usedGlobalVars.containsKey(edge)) {
				Set<VarDecl<?>> vars;
				var labels = edge.getLabels();
				if (labels.stream().anyMatch(label -> label instanceof XcfaLabel.AtomicBeginXcfaLabel)) {
					vars = getGlobalVarsWithBFS(edge, xcfaEdge -> xcfaEdge.getLabels().stream().noneMatch(label -> label instanceof XcfaLabel.AtomicEndXcfaLabel));
				} else {
					vars = getDirectlyUsedGlobalVars(edge);
				}
				usedGlobalVars.put(edge, vars);
			}
			return usedGlobalVars.get(edge);
		}

		/**
		 * Returns the global variables used by the given edge or by edges that are reachable via the given edge
		 * ("influenced global variables").
		 *
		 * @param edge whose successor edges' global variables are to be returned.
		 * @return the set of influenced global variables
		 */
		private Set<VarDecl<? extends Type>> getInfluencedGlobalVars(XcfaEdge edge) {
			if (!influencedGlobalVars.containsKey(edge)) {
				influencedGlobalVars.put(edge, getGlobalVarsWithBFS(edge, xcfaEdge -> true));
			}
			return influencedGlobalVars.get(edge);
		}

		/**
		 * Returns global variables encountered in a search starting from a given edge.
		 *
		 * @param startEdge the start point (edge) of the search
		 * @param visitEdge the predicate that tells whether an edge has to be explored
		 * @return the set of encountered global variables
		 */
		private Set<VarDecl<?>> getGlobalVarsWithBFS(XcfaEdge startEdge, Predicate<XcfaEdge> visitEdge) {
			Set<VarDecl<?>> vars = new HashSet<>();
			List<XcfaEdge> exploredEdges = new ArrayList<>();
			List<XcfaEdge> edgesToExplore = new ArrayList<>();
			edgesToExplore.add(startEdge);

			while (!edgesToExplore.isEmpty()) {
				var exploring = edgesToExplore.remove(0);
				vars.addAll(getDirectlyUsedGlobalVars(exploring));
				for (var newEdge : exploring.getTarget().getOutgoingEdges()) {
					if (!exploredEdges.contains(newEdge) && visitEdge.test(newEdge)) {
						edgesToExplore.add(newEdge);
					}
				}
				exploredEdges.add(exploring);
			}
			return vars;
		}
	}

	/**
	 * Backward edges in the XCFA (an edge of a loop).
	 */
	private final List<XcfaEdge> backwardEdges = new ArrayList<>();


	/**
	 * Collects backward edges of the given XCFA.
	 *
	 * @param xcfa the XCFA whose backward edges are to be collected
	 */
	private void collectBackwardEdges(XCFA xcfa) {
		for (var process : xcfa.getProcesses()) {
			for (var procedure : process.getProcedures()) {
				// DFS for every procedure of the XCFA to discover backward edges
				Set<XcfaLocation> visitedLocations = new HashSet<>();
				Stack<XcfaLocation> stack = new Stack<>();

				stack.push(procedure.getInitLoc()); // start from the initial location of the procedure
				while (!stack.isEmpty()) {
					XcfaLocation visiting = stack.pop();
					visitedLocations.add(visiting);
					for (var outgoingEdge : visiting.getOutgoingEdges()) {
						var target = outgoingEdge.getTarget();
						if (visitedLocations.contains(target)) { // backward edge
							backwardEdges.add(outgoingEdge);
						} else {
							stack.push(target);
						}
					}
				}
			}
		}
	}

}
