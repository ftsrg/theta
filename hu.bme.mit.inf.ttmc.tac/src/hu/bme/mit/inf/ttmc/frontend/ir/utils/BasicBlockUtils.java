package hu.bme.mit.inf.ttmc.frontend.ir.utils;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;
import java.util.function.Function;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class BasicBlockUtils {

	public static List<BasicBlock> reverseDFS(BasicBlock from, Function<BasicBlock, Boolean> pred) {
		Stack<BasicBlock> worklist = new Stack<>();
		List<BasicBlock> visited = new ArrayList<>();

		worklist.add(from);

		while (!worklist.isEmpty()) {
			BasicBlock current = worklist.pop();
			if (!visited.contains(current)) {
				if (pred.apply(current))
					return visited;

				visited.add(current);
				for (BasicBlock parent : current.parents()) {
					worklist.add(parent);
				}
			}
		}

		return visited;
	}

	public static List<BasicBlock> reverseDFS(BasicBlock from, BasicBlock to) {
		return reverseDFS(from, b -> b == to);
	}

}
