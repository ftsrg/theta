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
package hu.bme.mit.theta.xcfa.algorithm;

import com.google.common.collect.HashMultimap;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.algorithm.util.ProcessTransitionCollector;
import hu.bme.mit.theta.xcfa.algorithm.util.Tracer;
import hu.bme.mit.theta.xcfa.expl.AbstractExplState;
import hu.bme.mit.theta.xcfa.expl.ExplState;
import hu.bme.mit.theta.xcfa.expl.ProcessTransition;
import hu.bme.mit.theta.xcfa.expl.Transition;
import hu.bme.mit.theta.xcfa.expl.partialorder.DependencyRelation;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

/**
 * An explicit checker traversing every possible ordering of an XCFA state.
 * Supports only zero-initialized values (because of how ExplState works).
 */
public final class PartialOrderExplicitChecker {
	public PartialOrderExplicitChecker(XCFA xcfa) {
		this.xcfa = xcfa;
		factory = new AmpleSetFactory(xcfa);
	}

	private final AmpleSetFactory factory;
	private final XCFA xcfa;
	private final Stack<DfsNode> dfsStack = new Stack<>();
	private final Set<AbstractExplState> exploredStates = new HashSet<>();
	private final Set<AbstractExplState> stackedStates = new HashSet<>();

	/**
	 * Pushes the node to the stack if not explored before
	 */
	private void tryPushNode(DfsNode node) {
		ExplState state = node.getState();
		if (exploredStates.contains(state)) {
			return;
		}
		stackedStates.add(state.toImmutableExplState());
		exploredStates.add(state.toImmutableExplState());
		dfsStack.push(node);
	}

	private void popNode(DfsNode s0) {
		AbstractExplState state = dfsStack.pop().getState();
		assert (state.equals(s0.getState()));
		stackedStates.remove(state);
	}

	/**
	 * SafetyResult should be always unsafe OR finished.
	 */
	public SafetyResult<ExplState, Tracer.TransitionAction> check() {
		tryPushNode(new DfsNode(new ExplState(xcfa), null));
		while (!dfsStack.empty()) {
			DfsNode node = dfsStack.peek();
			if (node.hasChild()) {
				DfsNode child = node.child();
				if (stackedStates.contains(child.getState())) {
					// Cycle. Due to C3, we must expand the node
					if (!node.isExplicitlyExpanded()) {
						node.expand();
						continue;
					}
				}
				tryPushNode(child);
			} else {
				if (!node.isSafe()) {
					return Tracer.unsafe(dfsStack);
				}
				popNode(node);
			}
		}
		return Tracer.safe();
	}

	private static class AmpleSetFactory {
		// pre(Pi) I think
		private final Map<XCFA.Process, Collection<Transition>> allTransitionsByProcess;

		public AmpleSetFactory(XCFA xcfa) {
			allTransitionsByProcess = new HashMap<>();
			for (XCFA.Process process : xcfa.getProcesses()) {
				allTransitionsByProcess.put(process, ProcessTransitionCollector.getAllTransitionsByProcess(process));
			}
		}

		private void collectDependingProcesses(ProcessTransition t, Collection<XCFA.Process> alreadyProcessed,
											   Collection<XCFA.Process> result) {
			for (var x : allTransitionsByProcess.entrySet()) {
				if (alreadyProcessed.contains(x.getKey())) {
					continue;
				}
				if (x.getKey() == t.getProcess()) {
					continue;
				}
				if (DependencyRelation.depends(t, x.getValue())) {
					result.add(x.getKey());
				}
			}
		}

		// input is a non empty set of enabled transitions
		private Collection<Transition> collectAmpleSet(ExplState state, Collection<Transition> enabledTransitions) {
			HashSet<XCFA.Process> ampleSet = new HashSet<>();
			HashSet<XCFA.Process> notYetProcessed = new HashSet<>();


			HashMultimap<XCFA.Process, Transition> enabledTransitionsByProcess = HashMultimap.create();

			for (Transition pt : enabledTransitions) {
				if (!(pt instanceof ProcessTransition)) {
					return enabledTransitions;
				}
				enabledTransitionsByProcess.put(((ProcessTransition) pt).getProcess(), pt);
			}

			// add a transition
			ProcessTransition first = (ProcessTransition) enabledTransitions.iterator().next();
			notYetProcessed.add(first.getProcess());
			// add dependencies transitively
			while (!notYetProcessed.isEmpty()) {
				XCFA.Process toBeProcessed = notYetProcessed.iterator().next();
				ampleSet.add(toBeProcessed);
				Collection<Transition> transitions = state.getTransitionsOfProcess(toBeProcessed);
				notYetProcessed.remove(toBeProcessed);
				for (Transition enabledTransition : enabledTransitionsByProcess.get(toBeProcessed)) {
					collectDependingProcesses((ProcessTransition) enabledTransition, ampleSet, notYetProcessed);
				}
				// add disabled transitions' dependencies, which may activate the transition
				// more precisely: all processes' transitions that may enable
				// look at partialorder-test.xcfa for more information
				for (Transition tr : transitions) {
					if (enabledTransitions.contains(tr)) {
						continue;
					}
					// tr is disabled
					if (!(tr instanceof ProcessTransition)) {
						return enabledTransitions;
					}
					// tr is disabled ProcessTransition
					collectDependingProcesses((ProcessTransition) tr, ampleSet, notYetProcessed);
				}
			}
			Collection<Transition> result = new HashSet<>();
			for (XCFA.Process p : ampleSet) {
				result.addAll(enabledTransitionsByProcess.get(p));
			}
			return result;
		}

		// Does not contain the logic of C3 about cycles, they are handled in the DFS
		public Collection<Transition> returnAmpleSet(ExplState expl) {
			Collection<Transition> enabled = expl.getEnabledTransitions();
			if (enabled.size() == 0) {
				return Collections.emptySet();
			}
			return collectAmpleSet(expl, enabled);
		}
	}

	private final class DfsNode extends DfsNodeBase {

		private DfsNode(ExplState state, @Nullable Transition lastTransition) {
			super(state, lastTransition, factory.returnAmpleSet(state));
		}

		boolean isExpanded = false;

		public void expand() {
			isExpanded = true;
			resetWithTransitions(getState().getEnabledTransitions());
		}

		public boolean isExplicitlyExpanded() {
			return isExpanded;
		}

		@Override
		public DfsNode child() {
			Transition t = fetchNextTransition();
			return new DfsNode(getState().withTransitionExecuted(t), t);
		}
	}
}
