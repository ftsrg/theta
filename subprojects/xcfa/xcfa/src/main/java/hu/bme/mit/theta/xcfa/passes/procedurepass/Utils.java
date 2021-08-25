package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import static com.google.common.base.Preconditions.checkArgument;

public class Utils {
	public static Set<XcfaEdge> collectReverseEdges(XcfaLocation location) {
		return collectReverseEdges(location, new SetStack<>());
	}

	private static Set<XcfaEdge> collectReverseEdges(XcfaLocation location, SetStack<XcfaLocation> path) {
		Set<XcfaEdge> ret = new LinkedHashSet<>();
		path.push(location);
		List<XcfaEdge> outgoingEdges = location.getOutgoingEdges();
		for (XcfaEdge outgoingEdge : outgoingEdges) {
			if(!path.contains(outgoingEdge.getTarget())) {
				ret.addAll(collectReverseEdges(outgoingEdge.getTarget(), path));
			} else {
				ret.add(outgoingEdge);
			}
		}
		return ret;
	}

	/**
	 * This class can be used as a stack while using a Set for fast contains() performance
	 */
	private static class SetStack<T>{
		private final Stack<T> stack = new Stack<>();
		private final Set<T> set = new LinkedHashSet<>();

		public SetStack(SetStack<T> from) {
			from.stack.forEach(this.stack::push); // TODO: does this preserve order?
			set.addAll(from.set);
		}

		public SetStack(){}

		public void push(T t) {
			checkArgument(!set.contains(t), "SetStack can only hold unique elements!");
			stack.push(t);
			set.add(t);
		}
		public T pop() {
			T pop = stack.pop();
			set.remove(pop);
			return pop;
		}
		public T peek() {
			return stack.peek();
		}
		public boolean contains(T t) {
			return set.contains(t);
		}
	}
}
