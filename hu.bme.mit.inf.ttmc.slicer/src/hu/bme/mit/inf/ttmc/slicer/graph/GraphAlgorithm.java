package hu.bme.mit.inf.ttmc.slicer.graph;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.function.Consumer;
import java.util.function.Function;

public class GraphAlgorithm {

	public static <T extends GraphNode> List<T> DFS(T start)
	{
		Stack<T> stack = new Stack<>();
		List<T> visited = new ArrayList<>();

		stack.push(start);
		while (!stack.isEmpty()) {
			T node = stack.pop();
			if (!visited.contains(node)) {
				visited.add(node);
				for (GraphNode child : node.getChildren()) {
					stack.push((T) child);
				}
			}
		}

		return visited;
	}

	public static <T extends GraphNode> List<T> DFS(T start, Function<T, Boolean> func)
	{
		Stack<T> stack = new Stack<>();
		List<T> visited = new ArrayList<>();

		stack.push(start);
		while (!stack.isEmpty()) {
			T node = stack.pop();
			if (!visited.contains(node)) {
				if (func.apply(node))
					return visited; // Function required a stop

				visited.add(node);
				for (GraphNode child : node.getChildren()) {
					stack.push((T) child);
				}
			}
		}

		return visited;
	}

	public static <T extends ReversibleGraphNode> List<T> reverseDFS(T start)
	{
		Stack<T> stack = new Stack<>();
		List<T> visited = new ArrayList<>();

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

	public static <T extends ReversibleGraphNode> List<T> reverseDFS(T start, Function<T, Boolean> func)
	{
		Stack<T> stack = new Stack<>();
		List<T> visited = new ArrayList<>();

		stack.push(start);
		while (!stack.isEmpty()) {
			T node = stack.pop();
			if (!visited.contains(node)) {
				if (func.apply(node))
					return visited; // Function required a stop

				visited.add(node);
				for (GraphNode child : node.getParents()) {
					stack.push((T) child);
				}
			}
		}
		return visited;
	}

}
