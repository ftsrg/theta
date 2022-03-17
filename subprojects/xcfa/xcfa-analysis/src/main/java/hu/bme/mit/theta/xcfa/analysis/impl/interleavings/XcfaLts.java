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
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.*;
import java.util.AbstractMap.SimpleImmutableEntry;

public final class XcfaLts implements LTS<XcfaState<?>, XcfaAction> {

	private enum POR_MODE {
		POR_OFF, POR_STATIC
	}

	private final POR_MODE porMode = POR_MODE.POR_STATIC;

	// TODO global var query field in XcfaLts

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

			case POR_STATIC:
				List<SimpleImmutableEntry<XcfaEdge, Integer>> enabledEdges = new ArrayList<>();
				for (Integer enabledProcess : state.getEnabledProcesses()) {
					final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
					for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
						enabledEdges.add(new SimpleImmutableEntry<>(outgoingEdge, enabledProcess));
					}
				}

				Set<SimpleImmutableEntry<XcfaEdge, Integer>> minimalPersistentSet = null;
				for (var enabledEdge : enabledEdges) {
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
		GlobalVarQuery globalVarQuery = new GlobalVarQuery(startingEdge.getKey().getSource().getParent().getParent().getParent());

		Set<SimpleImmutableEntry<XcfaEdge, Integer>> persistentSet = new HashSet<>();
		Set<Integer> processesInPS = new HashSet<>();
		Set<VarDecl<? extends Type>> globalVarsInPS = new HashSet<>();
		List<SimpleImmutableEntry<XcfaEdge, Integer>> otherEdges = new ArrayList<>(enabledEdges);

		persistentSet.add(startingEdge);
		processesInPS.add(startingEdge.getValue());
		globalVarsInPS.addAll(globalVarQuery.getUsedGlobalVars(startingEdge.getKey(), true));
		otherEdges.remove(startingEdge);

		boolean addedNewEdge = true;
		while (addedNewEdge) {
			addedNewEdge = false;
			for (var action : otherEdges) {
				XcfaEdge edge = action.getKey();
				Integer process = action.getValue();

				if (processesInPS.contains(process)) {
					persistentSet.add(action);
					globalVarsInPS.addAll(globalVarQuery.getUsedGlobalVars(edge, true));
					otherEdges.remove(action);
					addedNewEdge = true;
				} else if (globalVarQuery.getInfluencedGlobalVars(edge).stream().anyMatch(globalVarsInPS::contains)) {
					persistentSet.add(action);
					processesInPS.add(process);
					globalVarsInPS.addAll(globalVarQuery.getUsedGlobalVars(edge, true));
					otherEdges.remove(action);
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
			globalVars = xcfa.getGlobalVars();
		}

		private Set<VarDecl<? extends Type>> getUsedGlobalVars(XcfaEdge edge, boolean store) {
			if (!usedGlobalVars.containsKey(edge)) {
				Set<VarDecl<?>> vars = new HashSet<>();
				edge.getLabels().forEach(label -> {
					LabelUtils.getVars(label).forEach(usedVar -> {
						if (globalVars.contains(usedVar)) {
							vars.add(usedVar);
						}
					});
				});
				if (store) usedGlobalVars.put(edge, vars);
			}
			return usedGlobalVars.get(edge);
		}

		private Set<VarDecl<? extends Type>> getInfluencedGlobalVars(XcfaEdge edge) {
			if (!influencedGlobalVars.containsKey(edge)) {
				Set<VarDecl<?>> vars = new HashSet<>();
				List<XcfaEdge> exploredEdges = new ArrayList<>();
				List<XcfaEdge> edgesToExplore = new ArrayList<>();
				edgesToExplore.add(edge);

				while (!edgesToExplore.isEmpty()) {
					var exploring = edgesToExplore.get(0);
					vars.addAll(getUsedGlobalVars(exploring, false));
					for (var newEdge : exploring.getTarget().getOutgoingEdges()) {
						if (!exploredEdges.contains(newEdge)) {
							edgesToExplore.add(newEdge);
						}
					}
					exploredEdges.add(exploring);
					edgesToExplore.remove(0);
				}
				influencedGlobalVars.put(edge, vars);
			}
			return influencedGlobalVars.get(edge);
		}
	}

}
