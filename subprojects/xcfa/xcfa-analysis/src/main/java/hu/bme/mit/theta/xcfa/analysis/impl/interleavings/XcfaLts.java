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
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.*;

public final class XcfaLts implements LTS<XcfaState<?>, XcfaAction> {

	private enum POR_MODE {
		POR_OFF, POR_STATIC
	}

	private final POR_MODE porMode = POR_MODE.POR_STATIC;

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
				ActionInterferenceGraph actionInterferenceGraph = new ActionInterferenceGraph();
				for (Integer enabledProcess : state.getEnabledProcesses()) {
					final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
					for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
						actionInterferenceGraph.addEdge(outgoingEdge, enabledProcess);
					}
				}
				for (var edge : actionInterferenceGraph.getMinimalComponent()) {
					final XcfaAction xcfaAction = XcfaAction.create(edge.getKey(), edge.getValue());
					xcfaActions.add(xcfaAction);
				}
				break;
		}
		return xcfaActions;
	}


	private static class ActionInterferenceGraph {
		private final List<AIGComponent> components = new ArrayList<>();

		public void addEdge(XcfaEdge outgoingEdge, Integer process) {
			AIGComponent firstComponent = null;
			for (AIGComponent component : components) {
				boolean added = component.addEdgeIfNeeded(outgoingEdge, process, firstComponent);
				if (added) {
					if (firstComponent == null) {
						firstComponent = component;
					} else {
						components.remove(component);
					}
				}
			}
		}

		public List<AbstractMap.SimpleImmutableEntry<Integer, XcfaEdge>> getMinimalComponent() {
			Comparator<AIGComponent> comparator = Comparator
					.comparing((AIGComponent c) -> c.actions.size())
					.thenComparing((AIGComponent c) -> c.parallelInterferences + c.conflictingActions)
					.thenComparing(c -> c.parallelInterferences);
			components.sort(comparator);
			return components.get(0).actions;
		}

		private static class AIGComponent {
			private final List<AbstractMap.SimpleImmutableEntry<Integer, XcfaEdge>> actions = new ArrayList<>();

			private int parallelInterferences = 0;
			private int conflictingActions = 0;

			private Set<VarDecl<?>> getUsedGlobalVars(XcfaEdge edge, List<VarDecl<? extends Type>> globalVars) {
				Set<VarDecl<?>> vars = new HashSet<>();
				edge.getLabels().forEach(label -> {
					LabelUtils.getVars(label).forEach(usedVar -> {
						if (globalVars.contains(usedVar)) {
							vars.add(usedVar);
						}
					});
				});
				return vars;
			}

			private boolean addEdgeIfNeeded(XcfaEdge edge, Integer process, AIGComponent mergeInto) {
				var globalVars = edge.getSource().getParent().getParent().getParent().getGlobalVars();
				var vars1 = getUsedGlobalVars(edge, globalVars);
				boolean add = false;
				for (var action : actions) {
					if (action.getKey().equals(process)) {
						conflictingActions++;
						add = true;
					} else {
						var vars2 = getUsedGlobalVars(action.getValue(), globalVars);
						if (vars1.stream().anyMatch(vars2::contains)) { // if they have common global variables
							parallelInterferences++;
							add = true;
						}
					}
				}
				if (add) {
					if (mergeInto == null) {
						actions.add(new AbstractMap.SimpleImmutableEntry<>(process, edge));
					} else {
						mergeInto.mergeComponent(this);
					}
				}
				return add;
			}

			private void mergeComponent(AIGComponent component) {
				actions.addAll(component.actions);
				parallelInterferences += component.parallelInterferences;
				conflictingActions += component.conflictingActions;
			}
		}
	}
}
