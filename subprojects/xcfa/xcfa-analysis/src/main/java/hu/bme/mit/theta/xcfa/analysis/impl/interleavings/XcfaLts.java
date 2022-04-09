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

	private enum POR_MODE {
		POR_OFF, POR_ON
	}

	private final POR_MODE porMode = POR_MODE.POR_ON;

	private GlobalVarQuery globalVarQuery = null;

	@Override
	public Collection<XcfaAction> getEnabledActionsFor(final XcfaState<?> state) {
		final List<XcfaAction> xcfaActions = new ArrayList<>();
		switch (porMode) {
			case POR_OFF:
				for (Integer enabledProcess : state.getEnabledProcesses()) {
					final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
					for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
						final XcfaAction xcfaAction = XcfaAction.create(enabledProcess, outgoingEdge);
						xcfaActions.add(xcfaAction);
					}
				}
				break;

			case POR_ON:
				List<SimpleImmutableEntry<XcfaEdge, Integer>> enabledEdges = new ArrayList<>();
				for (Integer enabledProcess : state.getEnabledProcesses()) {
					final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
					for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
						enabledEdges.add(new SimpleImmutableEntry<>(outgoingEdge, enabledProcess));
					}
				}

				if (globalVarQuery == null && enabledEdges.size() > 0) {
					XCFA xcfa = enabledEdges.get(0).getKey().getSource().getParent().getParent().getParent();
					globalVarQuery = new GlobalVarQuery(xcfa);
					collectBackwardEdges(xcfa);
				}
				Set<SimpleImmutableEntry<XcfaEdge, Integer>> minimalPersistentSet = null;
				for (var enabledEdge : enabledEdges) {
					// TODO small optimization: enough to start persistent set calculation from one edge per process
					Set<SimpleImmutableEntry<XcfaEdge, Integer>> persistentSet = calculatePersistentSet(enabledEdges, enabledEdge);
					if (minimalPersistentSet == null || persistentSet.size() < minimalPersistentSet.size()) {
						minimalPersistentSet = persistentSet;
					}
				}

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


	private Set<SimpleImmutableEntry<XcfaEdge, Integer>> calculatePersistentSet(List<SimpleImmutableEntry<XcfaEdge, Integer>> enabledEdges, SimpleImmutableEntry<XcfaEdge, Integer> startingEdge) {
		if (backwardEdges.contains(startingEdge.getKey())) return new HashSet<>(enabledEdges);

		Set<SimpleImmutableEntry<XcfaEdge, Integer>> persistentSet = new HashSet<>();
		Set<Integer> processesInPS = new HashSet<>();
		Set<VarDecl<? extends Type>> globalVarsInPS = new HashSet<>();
		List<SimpleImmutableEntry<XcfaEdge, Integer>> otherEdges = new ArrayList<>(enabledEdges);

		persistentSet.add(startingEdge);
		processesInPS.add(startingEdge.getValue());
		globalVarsInPS.addAll(globalVarQuery.getUsedGlobalVars(startingEdge.getKey()));
		otherEdges.remove(startingEdge);

		boolean addedNewEdge = true;
		while (addedNewEdge) {
			addedNewEdge = false;
			for (int i = 0; i < otherEdges.size(); i++) {
				SimpleImmutableEntry<XcfaEdge, Integer> action = otherEdges.get(i);
				XcfaEdge edge = action.getKey();
				Integer process = action.getValue();

				if (processesInPS.contains(process) || globalVarQuery.getInfluencedGlobalVars(edge).stream().anyMatch(globalVarsInPS::contains)) {
					if (backwardEdges.contains(edge)) return new HashSet<>(enabledEdges);

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


	private static class GlobalVarQuery {
		private final List<VarDecl<? extends Type>> globalVars;
		private final HashMap<XcfaEdge, Set<VarDecl<? extends Type>>> usedGlobalVars = new HashMap<>();
		private final HashMap<XcfaEdge, Set<VarDecl<? extends Type>>> influencedGlobalVars = new HashMap<>();

		GlobalVarQuery(XCFA xcfa) {
			System.out.println(xcfa.toDot());
			globalVars = xcfa.getGlobalVars();
		}

		private Set<VarDecl<? extends Type>> getDirectlyUsedGlobalVars(XcfaEdge edge) {
			Set<VarDecl<?>> vars = new HashSet<>();
			edge.getLabels().forEach(label -> LabelUtils.getVars(label).forEach(usedVar -> {
				if (globalVars.contains(usedVar)) {
					vars.add(usedVar);
				}
			}));
			return vars;
		}

		private Set<VarDecl<? extends Type>> getUsedGlobalVars(XcfaEdge edge) {
			if (!usedGlobalVars.containsKey(edge)) {
				Set<VarDecl<?>> vars;
				var labels = edge.getLabels();
				if (labels.stream().anyMatch(label -> label instanceof XcfaLabel.AtomicBeginXcfaLabel)) {
					vars = getVarsWithBFS(edge, xcfaEdge -> xcfaEdge.getLabels().stream().noneMatch(label -> label instanceof XcfaLabel.AtomicEndXcfaLabel));
				} else {
					vars = getDirectlyUsedGlobalVars(edge);
				}
				usedGlobalVars.put(edge, vars);
			}
			return usedGlobalVars.get(edge);
		}

		private Set<VarDecl<? extends Type>> getInfluencedGlobalVars(XcfaEdge edge) {
			if (!influencedGlobalVars.containsKey(edge)) {
				influencedGlobalVars.put(edge, getVarsWithBFS(edge, xcfaEdge -> true));
			}
			return influencedGlobalVars.get(edge);
		}

		private Set<VarDecl<?>> getVarsWithBFS(XcfaEdge startEdge, Predicate<XcfaEdge> visitEdge) {
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

	private final List<XcfaEdge> backwardEdges = new ArrayList<>();

	private void collectBackwardEdges(XCFA xcfa) {
		for (var process : xcfa.getProcesses()) {
			for (var procedure : process.getProcedures()) {
				// DFS for every procedure of the XCFA to discover backward edges
				Set<XcfaLocation> visitedLocations = new HashSet<>();
				Stack<XcfaLocation> stack = new Stack<>();

				stack.push(procedure.getInitLoc());
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
