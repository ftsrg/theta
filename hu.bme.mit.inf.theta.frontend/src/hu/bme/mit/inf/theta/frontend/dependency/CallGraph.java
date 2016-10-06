package hu.bme.mit.inf.theta.frontend.dependency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.ir.node.AssignNode;
import hu.bme.mit.inf.theta.frontend.ir.node.IrNode;

public final class CallGraph {

	public static class CallGraphNode {
		private final ProcDecl<?> proc;
		private final Map<CallGraphNode, List<IrNode>> targets = new HashMap<>();

		public CallGraphNode(ProcDecl<?> proc) {
			this.proc = proc;
		}

		public void addTarget(CallGraphNode target, IrNode call) {
			List<IrNode> callNodes = this.targets.get(target);
			if (callNodes == null) {
				callNodes = new ArrayList<>();
				this.targets.put(target, callNodes);
			}

			callNodes.add(call);
		}

		public ProcDecl<?> getProc() {
			return this.proc;
		}

		public Collection<CallGraphNode> getTargetNodes() {
			return Collections.unmodifiableCollection(this.targets.keySet());
		}

		@Override
		public String toString() {
			return this.targets.toString();
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
				for (IrNode node : block.getNodes()) {
					if (node instanceof AssignNode<?, ?> && ((AssignNode<?, ?>) node).getExpr() instanceof ProcCallExpr<?>) {
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

	public boolean isRecursive(Function function) {
		ProcDecl<?> proc = function.getProcDecl();

		CallGraphNode cgNode = this.nodes.get(proc);
		if (cgNode == null)
			throw new IllegalArgumentException(String.format("Function '%s' is not present in this call graph", function));

		return cgNode.targets.containsKey(cgNode);
	}

}
