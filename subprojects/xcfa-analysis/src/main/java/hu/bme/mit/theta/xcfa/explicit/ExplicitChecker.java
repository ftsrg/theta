package hu.bme.mit.theta.xcfa.explicit;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.simulator.*;

import java.util.*;

/**
 * An explicit checker traversing every possible ordering of an XCFA state.
 * Supports only zero-initialized values (because of how ExplState works).
 */
public class ExplicitChecker {

	private static class DfsNode {
		private final ExplState state;
		private final Iterator<Transition> nextTransition;

		private DfsNode(ExplState state) {
			this.state = state;
			nextTransition = state.getEnabledTransitions().iterator();
		}

		private boolean hasChild() {
			return
					state.getSafety().safe &&
							!state.getSafety().finished &&
							nextTransition.hasNext();
		}

		private boolean isSafe() {
			return state.getSafety().safe;
		}

		private DfsNode child() {
			Transition transition = nextTransition.next();
			return new DfsNode(state.executeTransition(transition));
		}
	}

	public static class SafetyResult {
		public final boolean safe;
		public final String message;
		public final List<Transition> trace;
		private SafetyResult() {
			safe = true;
			message = null;
			trace = null;
		}
		private SafetyResult(ExplState.StateSafety base, List<Transition> trace) {
			Preconditions.checkArgument(!base.safe,
					"SafetyResult should be built from an unsafe StateSafety");
			safe = base.safe;
			message = base.message;
			this.trace = trace;
		}

		@Override
		public String toString() {
			StringBuilder s = new StringBuilder();
			if (safe) {
				s.append("Safe");
			} else {
				s.append("Unsafe: ");
				s.append(message);
				s.append("\n");
				if (trace != null) {
					for (Transition t : trace) {
						s.append(t);
						s.append("\n");
					}
				}
			}
			return s.toString();
		}
	}

	/**
	 * SafetyResult should be always unsafe OR finished.
	 */
	public SafetyResult check(XCFA xcfa, boolean traced) {
		Set<AbstractExplState> exploredStates = new HashSet<>();
		// will be used in partial order reduction: Set<AbstractExplState> stackedStates = new HashSet<>();

		ExplState initialState;
		if (traced)
			initialState = new TracedExplState(xcfa);
		else
			initialState = new ExplState(xcfa);
		Stack<DfsNode> dfsStack = new Stack<>();
		dfsStack.push(new DfsNode(initialState));
		while (!dfsStack.empty()) {
			DfsNode node = dfsStack.peek();
			if (node.hasChild()) {
				DfsNode child = node.child();
				//ImmutableExplState ies = child.state.toImmutableExplState();
				if (exploredStates.contains(child.state)) {
					continue;
				}
				exploredStates.add(child.state.toImmutableExplState());
				dfsStack.push(child);
			} else {
				if (!node.isSafe()) {
					return new SafetyResult(node.state.getSafety(), node.state.getTrace());
				}
				dfsStack.pop();
			}
		}
		return new SafetyResult();
	}

}
