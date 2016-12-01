package hu.bme.mit.theta.frontend.c.dependency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import hu.bme.mit.theta.core.decl.ProcDecl;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.ProcRefExpr;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.GlobalContext;
import hu.bme.mit.theta.frontend.c.ir.node.AssignNode;
import hu.bme.mit.theta.frontend.c.ir.node.NonTerminatorIrNode;

public final class CallGraph {

	public static class CallGraphNode {
		private final ProcDecl<?> proc;
		private final Map<CallGraphNode, List<NonTerminatorIrNode>> targets = new HashMap<>();
		private final Map<CallGraphNode, List<NonTerminatorIrNode>> calls = new HashMap<>();

		public CallGraphNode(ProcDecl<?> proc) {
			this.proc = proc;
		}

		public void addTarget(CallGraphNode target, NonTerminatorIrNode call) {
			List<NonTerminatorIrNode> callNodes = this.targets.get(target);
			if (callNodes == null) {
				callNodes = new ArrayList<>();
				this.targets.put(target, callNodes);
				target.addCall(this, call);
			}

			callNodes.add(call);
		}

		public ProcDecl<?> getProc() {
			return this.proc;
		}

		public Collection<CallGraphNode> getTargetNodes() {
			return Collections.unmodifiableCollection(this.targets.keySet());
		}

		public Map<CallGraphNode, List<NonTerminatorIrNode>> getCalls() {
			return Collections.unmodifiableMap(this.calls);
		}

		public boolean isRecursive() {
			return this.targets.containsKey(this);
		}

		private void addCall(CallGraphNode caller, NonTerminatorIrNode call) {
			List<NonTerminatorIrNode> callNodes = this.targets.get(caller);
			if (callNodes == null) {
				callNodes = new ArrayList<>();
				this.calls.put(caller, callNodes);
			}

			callNodes.add(call);
		}

		@Override
		public String toString() {
			return this.proc.getName();
		}
	}

	private final GlobalContext context;
	private final Map<ProcDecl<?>, CallGraphNode> nodes;

	private CallGraph(GlobalContext context, Map<ProcDecl<?>, CallGraphNode> nodes) {
		this.context = context;
		this.nodes = nodes;
	}

	public static CallGraph buildCallGraph(GlobalContext context) {
		Map<ProcDecl<?>, CallGraphNode> nodes = new HashMap<>();

		for (Function func : context.functions()) {
			CallGraphNode cgNode = new CallGraphNode(func.getProcDecl());
			for (BasicBlock block : func.getBlocks()) {
				for (NonTerminatorIrNode node : block.getNodes()) {
					if (node instanceof AssignNode<?, ?>
							&& ((AssignNode<?, ?>) node).getExpr() instanceof ProcCallExpr<?>) {
						ProcCallExpr<?> procCall = (ProcCallExpr<?>) ((AssignNode<?, ?>) node).getExpr();
						ProcDecl<?> proc = ((ProcRefExpr<?>) procCall.getProc()).getDecl();

						CallGraphNode cgTarget = nodes.get(proc);
						if (cgTarget == null) {
							cgTarget = new CallGraphNode(proc);
							nodes.put(proc, cgTarget);
						}

						cgNode.addTarget(cgTarget, node);
					}
				}
			}
			nodes.put(func.getProcDecl(), cgNode);
		}

		CallGraph cg = new CallGraph(context, nodes);
		return cg;
	}

	public Collection<CallGraphNode> getNodes() {
		return Collections.unmodifiableCollection(this.nodes.values());
	}

	public List<CallGraphNode> getNodesDFS() {
		ProcDecl<?> main = this.context.getEntryPoint().getProcDecl();
		CallGraphNode mainNode = this.nodes.get(main);

		List<CallGraphNode> visited = new ArrayList<>();
		Stack<CallGraphNode> stack = new Stack<>();
		stack.push(mainNode);

		while (!stack.isEmpty()) {
			CallGraphNode cg = stack.pop();
			if (!visited.contains(cg)) {
				visited.add(cg);
				for (CallGraphNode child : cg.targets.keySet()) {
					stack.push(child);
				}
			}
		}

		return visited;
	}

	public boolean isRecursive(Function function) {
		ProcDecl<?> proc = function.getProcDecl();

		CallGraphNode cgNode = this.nodes.get(proc);
		if (cgNode == null)
			throw new IllegalArgumentException(
					String.format("Function '%s' is not present in this call graph", function));

		return cgNode.targets.containsKey(cgNode);
	}

	public boolean hasDefinition(CallGraphNode node) {
		return this.context.hasFunctionDefinition(node.getProc().getName());
	}

}
