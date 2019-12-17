package hu.bme.mit.theta.xcfa.explicit;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.simulator.ExplState;
import hu.bme.mit.theta.xcfa.simulator.Transition;

import java.util.Iterator;
import java.util.Stack;

/**
 * An explicit checker traversing every possible ordering of an XCFA state.
 * Supports only zero-initialized values (because of how ExplState works).
 */
public class ExplicitChecker {
	private static class DfsNode {
		private ExplState state;
		private Iterator<Transition> nextTransition;

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
			return new DfsNode(state.doTransition(transition));
		}
	}

	public class SafetyResult {
		public boolean safe;
		public String message;
		public SafetyResult() {
			safe = true;
			message = null;
		}
		public SafetyResult(ExplState.StateSafety base) {
			Preconditions.checkArgument(!base.safe,
					"SafetyResult should be built from an unsafe StateSafety");
			safe = base.safe;
			message = base.message;
		}
	}

	/**
	 * SafetyResult should be always unsafe OR finished.
	 */
	public SafetyResult check(XCFA xcfa) {
		ExplState initialState = new ExplState(xcfa);
		Stack<DfsNode> dfsStack = new Stack<>();
		dfsStack.push(new DfsNode(initialState));
		while (!dfsStack.empty()) {
			DfsNode node = dfsStack.peek();
			if (node.hasChild()) {
				dfsStack.push(node.child());
			} else {
				if (!node.isSafe()) {
					return new SafetyResult(node.state.getSafety());
				}
				dfsStack.pop();
			}
		}
		return new SafetyResult();
	}
}
