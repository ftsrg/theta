package hu.bme.mit.theta.xcfa.explicit;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.simulator.ErrorReachedException;
import hu.bme.mit.theta.xcfa.simulator.RuntimeState;
import hu.bme.mit.theta.xcfa.simulator.Transition;

import java.util.Collection;
import java.util.Iterator;
import java.util.Stack;

public class ExplicitChecker {
	public ExplicitChecker(XCFA xcfa) throws ErrorReachedException {
		RuntimeState state = new RuntimeState(xcfa);
		dfs(state);
	}

	private static class DfsNode {
		private RuntimeState state;
		private Iterator<Transition> nextTransition;

		private DfsNode(RuntimeState state) throws ErrorReachedException {
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

	private void dfs(RuntimeState s) throws ErrorReachedException {
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
