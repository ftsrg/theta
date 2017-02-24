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

		public CallGraphNode(final ProcDecl<?> proc) {
			this.proc = proc;
		}

		public void addTarget(final CallGraphNode target, final NonTerminatorIrNode call) {
			List<NonTerminatorIrNode> callNodes = this.targets.get(target);
			if (callNodes == null) {
				callNodes = new ArrayList<>();
				this.targets.put(target, callNodes);
			}

			callNodes.add(call);
			target.addCall(this, call);
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

		private void addCall(final CallGraphNode caller, final NonTerminatorIrNode call) {
			List<NonTerminatorIrNode> callNodes = this.calls.get(caller);
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

	private CallGraph(final GlobalContext context, final Map<ProcDecl<?>, CallGraphNode> nodes) {
		this.context = context;
		this.nodes = nodes;
	}

	public static CallGraph buildCallGraph(final GlobalContext context) {
		final Map<ProcDecl<?>, CallGraphNode> nodes = new HashMap<>();

		for (final Function func : context.functions()) {
			final CallGraphNode cg = new CallGraphNode(func.getProcDecl());
			nodes.put(func.getProcDecl(), cg);
		}

		for (final Function func : context.functions()) {
			final CallGraphNode cgNode = nodes.get(func.getProcDecl());
			for (final BasicBlock block : func.getBlocks()) {
				for (final NonTerminatorIrNode node : block.getNodes()) {
					if (node instanceof AssignNode<?, ?>
							&& ((AssignNode<?, ?>) node).getExpr() instanceof ProcCallExpr<?>) {
						final ProcCallExpr<?> procCall = (ProcCallExpr<?>) ((AssignNode<?, ?>) node).getExpr();
						final ProcDecl<?> proc = ((ProcRefExpr<?>) procCall.getProc()).getDecl();

						CallGraphNode cgTarget = nodes.get(proc);
						if (cgTarget == null) {
							cgTarget = new CallGraphNode(proc);
							nodes.put(proc, cgTarget);
						}

						cgNode.addTarget(cgTarget, node);
					}
				}
			}
		}

		final CallGraph cg = new CallGraph(context, nodes);
		return cg;
	}

	public Collection<CallGraphNode> getNodes() {
		return Collections.unmodifiableCollection(this.nodes.values());
	}

	public List<CallGraphNode> getNodesDFS() {
		final ProcDecl<?> main = this.context.getEntryPoint().getProcDecl();
		final CallGraphNode mainNode = this.nodes.get(main);

		final List<CallGraphNode> visited = new ArrayList<>();
		final Stack<CallGraphNode> stack = new Stack<>();
		stack.push(mainNode);

		while (!stack.isEmpty()) {
			final CallGraphNode cg = stack.pop();
			if (!visited.contains(cg)) {
				visited.add(cg);
				for (final CallGraphNode child : cg.targets.keySet()) {
					stack.push(child);
				}
			}
		}

		return visited;
	}

	public boolean isRecursive(final Function function) {
		final ProcDecl<?> proc = function.getProcDecl();

		final CallGraphNode cgNode = this.nodes.get(proc);
		if (cgNode == null)
			throw new IllegalArgumentException(
					String.format("Function '%s' is not present in this call graph", function));

		return cgNode.targets.containsKey(cgNode);
	}

	public boolean hasDefinition(final CallGraphNode node) {
		return this.context.hasFunctionDefinition(node.getProc().getName());
	}

}
