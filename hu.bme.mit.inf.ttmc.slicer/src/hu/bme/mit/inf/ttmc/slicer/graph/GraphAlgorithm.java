package hu.bme.mit.inf.ttmc.slicer.graph;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

public class GraphAlgorithm {

	public static Set<? extends GraphNode> DFS(GraphNode start)
	{
		Stack<GraphNode> stack = new Stack<GraphNode>();
		Set<GraphNode> visited = new HashSet<>();

		stack.push(start);
		while (!stack.isEmpty()) {
			GraphNode node = stack.pop();
			if (!visited.contains(node)) {
				visited.add(node);
				for (GraphNode child : node.getChildren()) {
					stack.push(child);
				}
			}
		}

		return visited;
	}

	public static <T extends ReversibleGraphNode> Set<T> reverseDFS(T start)
	{
		Stack<T> stack = new Stack<>();
		Set<T> visited = new HashSet<>();

		stack.push(start);
		while (!stack.isEmpty()) {
			T node = stack.pop();
			if (!visited.contains(node)) {
				visited.add(node);
				for (ReversibleGraphNode child : node.getParents()) {
					stack.push((T) child);
				}
			}
		}

		return visited;
	}

}
