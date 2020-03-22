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

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.algorithm.util.Tracer;
import hu.bme.mit.theta.xcfa.expl.AbstractExplState;
import hu.bme.mit.theta.xcfa.expl.ExplState;
import hu.bme.mit.theta.xcfa.expl.Transition;

import javax.annotation.Nullable;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

/**
 * An explicit checker traversing every possible ordering of an XCFA state.
 * Supports only zero-initialized values (because of how ExplState works).
 */
public final class ExplicitChecker {

	private static final class DfsNode extends DfsNodeBase {

		private DfsNode(ExplState state, @Nullable Transition lastTransition) {
			super(state, lastTransition, state.getEnabledTransitions());
		}

		@Override
		public DfsNode child() {
			Transition t = fetchNextTransition();
			return new DfsNode(getState().executeTransition(t), t);
		}
	}

	private XCFA xcfa;
	private boolean debug;

	public ExplicitChecker(XCFA xcfa) {
		this(xcfa, false);
	}

	public ExplicitChecker(XCFA xcfa, boolean debug) {
		this.xcfa = xcfa;
		this.debug = debug;
	}

	private static void debugPrint(ExplState s, boolean debug) {
		if (!debug)
			return;
		System.out.println(s);
		System.out.println("Enabled transitions:");
		for (var tr : s.getEnabledTransitions()) {
			System.out.println(tr);
		}
		System.out.println();
	}

	private Set<AbstractExplState> exploredStates = new HashSet<>();
	private Stack<DfsNode> dfsStack = new Stack<>();

	private void tryPushNode(DfsNode node) {
		ExplState state = node.getState();
		if (exploredStates.contains(state)) {
			return;
		}
		debugPrint(state, debug);
		exploredStates.add(state.toImmutableExplState());
		dfsStack.push(node);
	}

	private void popNode(DfsNode s0) {
		AbstractExplState state = dfsStack.pop().getState();
		assert(state.equals(s0.getState()));
	}

	/**
	 * SafetyResult should be always unsafe OR finished.
	 */
	public SafetyResult<ExplState, Tracer.TransitionAction> check() {

		tryPushNode(new DfsNode(new ExplState(xcfa), null));

		while (!dfsStack.empty()) {
			DfsNode node = dfsStack.peek();
			if (node.hasChild()) {
				tryPushNode(node.child());
			} else {
				if (!node.isSafe()) {
					return Tracer.unsafe(dfsStack);
				}
				popNode(node);
			}
		}
		return Tracer.safe();
	}

}
