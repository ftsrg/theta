package hu.bme.mit.theta.frontend.c.transform;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import hu.bme.mit.theta.common.Product3;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.ProcDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.ProcRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph.CallGraphNode;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.GlobalContext;
import hu.bme.mit.theta.frontend.c.ir.node.AssignNode;
import hu.bme.mit.theta.frontend.c.ir.node.EntryNode;
import hu.bme.mit.theta.frontend.c.ir.node.NodeFactory;
import hu.bme.mit.theta.frontend.c.ir.node.NonTerminatorIrNode;
import hu.bme.mit.theta.frontend.c.ir.node.ReturnNode;

public class FunctionInliner implements Transformer {

	private static class FunctionInlineInfo {
		public AssignNode<?, ?> node;
		public Function function;
		public ProcDecl<?> proc;

		public FunctionInlineInfo(AssignNode<?, ?> node, Function function, ProcDecl<?> proc) {
			this.node = node;
			this.function = function;
			this.proc = proc;
		}
	}

	@Override
	public void transform(GlobalContext context) {		
		CallGraph cg = CallGraph.buildCallGraph(context);
		List<CallGraphNode> inlineables = cg.getNodesDFS().stream()
				.filter(n -> !n.isRecursive()) // recursive functions cannot be inlined at the moment
				// TODO
				.filter(n -> cg.hasDefinition(n)) // we can only inline functions with definitions
				.filter(n -> !n.getProc().getName().equals("main")) // never inline the entry function
				.collect(Collectors.toList());
		Collections.reverse(inlineables); // start with the leaves of the DFS search tree
		
		for (CallGraphNode calleeCg : inlineables) {
			ProcDecl<?> calleeProc = calleeCg.getProc();
			Function func = context.getFunctionByName(calleeCg.getProc().getName());
			for (Entry<CallGraphNode, List<NonTerminatorIrNode>> callInfo : calleeCg.getCalls().entrySet()) {
				ProcDecl<?> callerProc = callInfo.getKey().getProc();
				Function caller = context.getFunctionByProc(callerProc);

				for (NonTerminatorIrNode node : callInfo.getValue()) {
					BasicBlock block = node.getParentBlock();
					int idx = block.getNodeIndex(node);

					Product3<BasicBlock, BasicBlock, BasicBlock> tuple = caller.splitBlock(block, idx);

					List<? extends ParamDecl<?>> params = calleeProc.getParamDecls();
					Map<VarDecl<? extends Type>, Expr<? extends Type>> boundParams = new HashMap<>();

					AssignNode<?, ?> callNode = (AssignNode<?, ?>) node;
					ProcCallExpr<?> callExpr = (ProcCallExpr<?>) callNode.getExpr();

					for (int i = 0; i < params.size(); ++i) {
						ParamDecl<?> param = params.get(i);
						VarDecl<? extends Type> var = func.getArgument(param);
						Expr<? extends Type> expr = callExpr.getParams().get(i);

						boundParams.put(var, expr);
					}

					// VariableRefactorExprVisitor visitor = new
					// VariableRefactorExprVisitor("inline" + inlineId++,
					// boundParams);
					Function copy = func.copy();

					List<BasicBlock> copyBlocks = copy.getBlocksDFS().stream().filter(b -> b != copy.getEntryBlock())
							.filter(b -> b != copy.getExitBlock()).collect(Collectors.toList());

					for (BasicBlock copyBlock : copyBlocks) {
						caller.addBasicBlock(copyBlock);

						if (copyBlock.getTerminator() instanceof ReturnNode) {
							ReturnNode ret = (ReturnNode) copyBlock.getTerminator();
							copyBlock.clearTerminator();
							copyBlock.addNode(NodeFactory.Assign(callNode.getVar(), ret.getExpr()));
							copyBlock.terminate(NodeFactory.Goto(tuple._3()));
						}
					}

					// Create a new entry child, assigning local variables the
					// values of the function call
					BasicBlock inlineEntry = copy.createBlock("inline_entry");
					for (Entry<VarDecl<? extends Type>, Expr<? extends Type>> bp : boundParams.entrySet()) {
						VarDecl<? extends Type> var = bp.getKey();
						Expr<? extends Type> expr = bp.getValue();

						inlineEntry.addNode(NodeFactory.Assign(var, expr));
					}

					EntryNode entryNode = (EntryNode) copy.getEntryBlock().getTerminator();
					BasicBlock entryTarget = entryNode.getTarget();

					entryTarget.removeParent(copy.getEntryBlock());
					inlineEntry.terminate(NodeFactory.Goto(entryTarget));
					tuple._1().clearTerminator();
					tuple._1().terminate(NodeFactory.Goto(inlineEntry));

					// There can be only one entry child
					copy.getEntryBlock().children().forEach(child -> {
						child.removeParent(copy.getEntryBlock());
					});

					List<BasicBlock> exitParents = new ArrayList<>(copy.getExitBlock().parents());
					exitParents.forEach(parent -> {
						parent.getTerminator().replaceTarget(copy.getExitBlock(), tuple._3());

					});
					caller.normalize();
				}

			}

			// This function is no longer needed
			func.disable();
		}

	}

	private void transformFunction(Function function) {
		GlobalContext context = function.getContext();
		List<FunctionInlineInfo> inlinables = new ArrayList<>();

		for (BasicBlock block : function.getBlocksDFS()) {
			for (NonTerminatorIrNode node : block.getNodes()) {
				// Function calls are never nested inside complex expressions
				if (node instanceof AssignNode<?, ?>) {
					AssignNode<?, ?> assign = (AssignNode<?, ?>) node;
					if (assign.getExpr() instanceof ProcCallExpr<?>) {
						ProcDecl<?> proc = this.findProcDecl((ProcCallExpr<?>) assign.getExpr());
						Function target = context.getFunctionByName(proc.getName());

						if (target != null)
							inlinables.add(new FunctionInlineInfo(assign, target, proc));

						// If the function definition was not found, we cannot
						// inline it
					}
				}
			}
		}

		for (FunctionInlineInfo info : inlinables) {
			final AssignNode<?, ?> node = info.node;
			final BasicBlock block = node.getParentBlock();
			final ProcCallExpr<?> call = (ProcCallExpr<?>) node.getExpr();

			int idx = block.getNodeIndex(node);
			// tuple(before, split, after)
			Product3<BasicBlock, BasicBlock, BasicBlock> tuple = function.splitBlock(block, idx);

			List<? extends ParamDecl<?>> params = info.function.getProcDecl().getParamDecls();
			Map<VarDecl<? extends Type>, Expr<? extends Type>> boundParams = new HashMap<>();

			for (int i = 0; i < params.size(); ++i) {
				ParamDecl<?> param = params.get(i);
				VarDecl<? extends Type> var = info.function.getArgument(param);
				Expr<? extends Type> expr = call.getParams().get(i);

				boundParams.put(var, expr);
			}

			// VariableRefactorExprVisitor visitor = new
			// VariableRefactorExprVisitor("inline" + inlineId++, boundParams);
			Function copy = info.function.copy();

			List<BasicBlock> copyBlocks = copy.getBlocksDFS().stream().filter(b -> b != copy.getEntryBlock())
					.filter(b -> b != copy.getExitBlock()).collect(Collectors.toList());

			for (BasicBlock copyBlock : copyBlocks) {
				function.addBasicBlock(copyBlock);

				if (copyBlock.getTerminator() instanceof ReturnNode) {
					ReturnNode ret = (ReturnNode) copyBlock.getTerminator();
					copyBlock.clearTerminator();
					copyBlock.addNode(NodeFactory.Assign(node.getVar(), ret.getExpr()));
					copyBlock.terminate(NodeFactory.Goto(tuple._3()));
				}
			}

			// Create a new entry child, assigning local variables the values of
			// the function call
			BasicBlock inlineEntry = copy.createBlock("inline_entry");
			for (Entry<VarDecl<? extends Type>, Expr<? extends Type>> bp : boundParams.entrySet()) {
				VarDecl<? extends Type> var = bp.getKey();
				Expr<? extends Type> expr = bp.getValue();

				inlineEntry.addNode(NodeFactory.Assign(var, expr));
			}

			EntryNode entryNode = (EntryNode) copy.getEntryBlock().getTerminator();
			BasicBlock entryTarget = entryNode.getTarget();

			entryTarget.removeParent(copy.getEntryBlock());
			inlineEntry.terminate(NodeFactory.Goto(entryTarget));
			tuple._1().clearTerminator();
			tuple._1().terminate(NodeFactory.Goto(inlineEntry));

			// There can be only one entry child
			copy.getEntryBlock().children().forEach(child -> {
				child.removeParent(copy.getEntryBlock());
			});

			List<BasicBlock> exitParents = new ArrayList<>(copy.getExitBlock().parents());
			exitParents.forEach(parent -> {
				parent.getTerminator().replaceTarget(copy.getExitBlock(), tuple._3());

			});
		}

		function.normalize();
	}

	private ProcDecl<?> findProcDecl(ProcCallExpr<?> call) {
		// TODO: Why is this cast even needed?
		ProcRefExpr<?> ref = (ProcRefExpr<?>) call.getProc();

		return ref.getDecl();
	}

	@Override
	public String getTransformationName() {
		return "FunctionInline";
	}

}
