package hu.bme.mit.theta.xcfa.explicit;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.simulator.RuntimeState;
import hu.bme.mit.theta.xcfa.simulator.Transition;

import java.util.Iterator;
import java.util.Stack;

// TODO add capability for checking for deadlocks
// TODO error location reachability should not throw AssertionError
public class ExplicitChecker {
	public ExplicitChecker(XCFA xcfa) {
		RuntimeState state = new RuntimeState(xcfa);
		dfs(state);
	}

	private static class DfsNode {
		RuntimeState state;
		Iterator<Transition> nextTransition;

		DfsNode(RuntimeState state) {
			this.state = state;
			nextTransition = state.getEnabledTransitions().iterator();
		}

		boolean hasChild() {
			return nextTransition.hasNext();
		}

		DfsNode child() {
			RuntimeState newState = new RuntimeState(state);
			nextTransition.next().step(newState);
			return new DfsNode(newState);
		}
	}

	private void dfs(RuntimeState s) {
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
