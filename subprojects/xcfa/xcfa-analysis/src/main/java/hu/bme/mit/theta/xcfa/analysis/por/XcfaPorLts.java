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

package hu.bme.mit.theta.xcfa.analysis.por;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.PorLts;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.*;

import java.util.*;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.xcfa.UtilsKt.collectVars;
import static hu.bme.mit.theta.xcfa.UtilsKt.getFlatLabels;
import static hu.bme.mit.theta.xcfa.analysis.XcfaAnalysisKt.getXcfaLts;

public class XcfaPorLts extends PorLts<XcfaState<?>, XcfaAction, XcfaEdge> {

	private final XCFA xcfa;

	private final LTS<XcfaState<?>, XcfaAction> simpleXcfaLts = getXcfaLts();

	private final Random random = new Random();

	public XcfaPorLts(XCFA xcfa) {
		this.xcfa = xcfa;
		collectBackwardTransitions();
	}

	@Override
	protected Set<XcfaAction> getAllEnabledActionsFor(XcfaState<?> state) {
		return simpleXcfaLts.getEnabledActionsFor(state);
	}

	@Override
	protected Collection<Collection<XcfaAction>> getPersistentSetFirstActions(Collection<XcfaAction> allEnabledActions) {
		var enabledActionsByProcess = allEnabledActions.stream().collect(Collectors.groupingBy(XcfaAction::getPid));
		List<Integer> enabledProcesses = new ArrayList<>(enabledActionsByProcess.keySet());
		Collections.shuffle(enabledProcesses, random);
		Collection<Collection<XcfaAction>> firstActions = new HashSet<>();

		for (Integer enabledProcess : enabledProcesses) {
			var actionsByProcess = enabledActionsByProcess.get(enabledProcess);
			firstActions.add(actionsByProcess);
		}
		return firstActions;
	}

	@Override
	protected boolean canEnOrDisableEachOther(XcfaAction action1, XcfaAction action2) {
		return action1.getPid() == action2.getPid();
	}

	@Override
	protected XcfaEdge getTransitionOf(XcfaAction action) {
		return action.getEdge();
	}

	@Override
	protected Set<XcfaEdge> getSuccessiveTransitions(XcfaEdge edge) {
		var outgoingEdges = new HashSet<>(edge.getTarget().getOutgoingEdges());
		List<StartLabel> startThreads = getFlatLabels(edge).stream()
				.filter(label -> label instanceof StartLabel)
				.map(label -> (StartLabel) label).toList();
		if (startThreads.size() > 0) { // for start thread labels, the thread procedure must be explored, too!
			startThreads.forEach(startThread ->
					outgoingEdges.addAll(xcfa.getProcedures().stream().filter(it -> it.getName().equals(startThread.getName())).findFirst().get().getInitLoc().getOutgoingEdges()));
		}
		return outgoingEdges;
	}

	/**
	 * Returns the global variables that an edge uses (it is present in one of its labels).
	 *
	 * @param edge whose global variables are to be returned
	 * @return the set of used global variables
	 */
	@Override
	protected Set<VarDecl<? extends Type>> getDirectlyUsedSharedObjects(XcfaEdge edge) {
		Set<VarDecl<?>> vars = new HashSet<>();
		getFlatLabels(edge).forEach(label -> collectVars(label).forEach(usedVar -> {
			if (xcfa.getVars().stream().map(XcfaGlobalVar::getWrappedVar).anyMatch(it -> it.equals(usedVar))) {
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
	@Override
	protected Set<? extends Decl<? extends Type>> getUsedSharedObjects(XcfaEdge edge) {
		Set<? extends Decl<? extends Type>> vars;
		var labels = getFlatLabels(edge);
		if (labels.stream().anyMatch(label -> label instanceof FenceLabel && ((FenceLabel) label).getLabels().contains("ATOMIC_BEGIN"))) {
			vars = getSharedObjectsWithBFS(edge, xcfaEdge -> getFlatLabels(xcfaEdge).stream().noneMatch(label -> label instanceof FenceLabel && ((FenceLabel) label).getLabels().contains("ATOMIC_END")));
		} else {
			vars = getDirectlyUsedSharedObjects(edge);
		}
		return vars;
	}

	/**
	 * Collects backward edges of the given XCFA.
	 */
	@Override
	protected void collectBackwardTransitions() {
		for (var procedure : xcfa.getProcedures()) {
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
						backwardTransitions.add(outgoingEdge);
					} else {
						stack.push(target);
					}
				}
			}
		}
	}
}
