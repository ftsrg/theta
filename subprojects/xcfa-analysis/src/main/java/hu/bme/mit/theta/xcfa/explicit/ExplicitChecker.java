package hu.bme.mit.theta.xcfa.explicit;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.simulator.ErrorReachedException;
import hu.bme.mit.theta.xcfa.simulator.ExplState;
import hu.bme.mit.theta.xcfa.simulator.Transition;

import java.util.Collection;
import java.util.Iterator;
import java.util.Stack;

/**
 * An explicit checker traversing every possible ordering of an XCFA state.
 * Supports only zero-initialized values (because of how ExplState works).
 */
public class ExplicitChecker {
	public ExplicitChecker(XCFA xcfa) throws ErrorReachedException {
		ExplState state = new ExplState(xcfa);
		dfs(state);
	}

	private static class DfsNode {
		private ExplState state;
		private Iterator<Transition> nextTransition;

		private DfsNode(ExplState state) throws ErrorReachedException {
			this.state = state;
			Collection<Transition> transitions = state.getEnabledTransitions();
			if (transitions.size() == 0 && !state.isFinished()) {
				throw new ErrorReachedException("Deadlock caught");
			}
			nextTransition = state.getEnabledTransitions().iterator();
		}

		private boolean hasChild() {
			return nextTransition.hasNext();
		}

		private DfsNode child() throws ErrorReachedException {
			Transition transition = nextTransition.next();
			return new DfsNode(state.doTransition(transition));
		}
	}

	private void dfs(ExplState s) throws ErrorReachedException {
		Stack<DfsNode> dfsStack = new Stack<>();
		dfsStack.push(new DfsNode(s));
		while (!dfsStack.empty()) {
			DfsNode node = dfsStack.peek();
			if (node.hasChild()) {
				dfsStack.push(node.child());
			} else {
				dfsStack.pop();
			}
		}
	}
}
