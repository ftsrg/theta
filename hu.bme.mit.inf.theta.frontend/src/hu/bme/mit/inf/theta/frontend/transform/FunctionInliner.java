package hu.bme.mit.inf.theta.frontend.transform;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.common.Product3;
import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.theta.frontend.dependency.CallGraph;
import hu.bme.mit.inf.theta.frontend.dependency.CallGraph.CallGraphNode;
import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.ir.node.AssignNode;
import hu.bme.mit.inf.theta.frontend.ir.node.EntryNode;
import hu.bme.mit.inf.theta.frontend.ir.node.IrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.NodeFactory;
import hu.bme.mit.inf.theta.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.ReturnNode;
import hu.bme.mit.inf.theta.frontend.ir.utils.IrPrinter;
import hu.bme.mit.inf.theta.frontend.transform.expr.VariableRefactorExprVisitor;

public class FunctionInliner implements ContextTransformer {

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
		List<CallGraphNode> inlineables = cg.getNodesDFS()
				.stream()
				.filter(n -> !n.isRecursive())
				.filter(n -> cg.hasDefinition(n))
				.filter(n -> !n.getProc().getName().equals("main")) // TODO: Valami szofisztikáltabb jó lenne
				.collect(Collectors.toList());
		Collections.reverse(inlineables);

		for (CallGraphNode callerCg : inlineables) {
			ProcDecl<?> calleeProc = callerCg.getProc();
			Function func = context.getFunctionByName(callerCg.getProc().getName());
			for (Entry<CallGraphNode, List<NonTerminatorIrNode>> callInfo : callerCg.getCalls().entrySet()) {
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


					//VariableRefactorExprVisitor visitor = new VariableRefactorExprVisitor("inline" + inlineId++, boundParams);
					Function copy = func.copy();

					List<BasicBlock> copyBlocks = copy.getBlocksDFS().stream()
						.filter(b -> b != copy.getEntryBlock())
						.filter(b -> b != copy.getExitBlock())
						.collect(Collectors.toList());

					for (BasicBlock copyBlock : copyBlocks) {
						caller.addBasicBlock(copyBlock);

						if (copyBlock.getTerminator() instanceof ReturnNode) {
							ReturnNode ret = (ReturnNode) copyBlock.getTerminator();
							copyBlock.clearTerminator();
							copyBlock.addNode(NodeFactory.Assign(callNode.getVar(), ret.getExpr()));
							copyBlock.terminate(NodeFactory.Goto(tuple._3()));
						}
					}

					// Create a new entry child, assigning local variables the values of the function call
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

				caller.normalize();
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

						// If the function definition was not found, we cannot inline it
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


			//VariableRefactorExprVisitor visitor = new VariableRefactorExprVisitor("inline" + inlineId++, boundParams);
			Function copy = info.function.copy();


			List<BasicBlock> copyBlocks = copy.getBlocksDFS().stream()
				.filter(b -> b != copy.getEntryBlock())
				.filter(b -> b != copy.getExitBlock())
				.collect(Collectors.toList());

			for (BasicBlock copyBlock : copyBlocks) {
				function.addBasicBlock(copyBlock);

				if (copyBlock.getTerminator() instanceof ReturnNode) {
					ReturnNode ret = (ReturnNode) copyBlock.getTerminator();
					copyBlock.clearTerminator();
					copyBlock.addNode(NodeFactory.Assign(node.getVar(), ret.getExpr()));
					copyBlock.terminate(NodeFactory.Goto(tuple._3()));
				}
			}

			// Create a new entry child, assigning local variables the values of the function call
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
