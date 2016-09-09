package hu.bme.mit.inf.theta.frontend.cfa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.impl.Exprs;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.inf.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.inf.theta.formalism.cfa.impl.MutableCfa;
import hu.bme.mit.inf.theta.formalism.common.stmt.impl.Stmts;
import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.node.AssertNode;
import hu.bme.mit.inf.theta.frontend.ir.node.AssignNode;
import hu.bme.mit.inf.theta.frontend.ir.node.BranchTableNode;
import hu.bme.mit.inf.theta.frontend.ir.node.BranchTableNode.BranchTableEntry;
import hu.bme.mit.inf.theta.frontend.ir.node.EntryNode;
import hu.bme.mit.inf.theta.frontend.ir.node.ExitNode;
import hu.bme.mit.inf.theta.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.theta.frontend.ir.node.IrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.theta.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.ReturnNode;
import hu.bme.mit.inf.theta.frontend.ir.node.TerminatorIrNode;

/**
 * A utility class for function to CFA (control flow automata) transformations
 *
 * @author Gyula Sallai <salla016@gmail.com>
 */
public class FunctionToCFATransformer {

	public static CFA createLBE(Function func) {
		MutableCfa cfa = new MutableCfa();
		List<BasicBlock> blocks = func.getBlocksDFS();
		Map<BasicBlock, CfaLoc> mapping = new HashMap<>();

		blocks.forEach(block -> mapping.put(block, cfa.createLoc()));

		BasicBlock entry = func.getEntryBlock();
		BasicBlock exit = func.getExitBlock();

		// Replace the initial node
		cfa.removeLoc(mapping.get(entry));
		cfa.removeLoc(mapping.get(exit));
		mapping.put(entry, cfa.getInitLoc());
		mapping.put(exit, cfa.getFinalLoc());

		for (BasicBlock block : blocks) {
			CfaLoc source = mapping.get(block);
			for (BasicBlock child : block.children()) {
				CfaLoc target = mapping.get(child);

			}
		}

		return cfa;
	}

	/**
	 * Creates a singe-block encoded CFA from an input function
	 *
	 * @param func The function to transform
	 *
	 * @return A CFA instance semantically equivalent to the given function
	 */
	public static CFA createSBE(Function func) {
		MutableCfa cfa = new MutableCfa();
		Map<IrNode, CfaLoc> mapping = new HashMap<>();
		List<BasicBlock> blocks = func.getBlocksDFS();
		blocks.remove(func.getEntryBlock());

		// Initialize the CFA locations
		for (BasicBlock block : blocks) {
			for (IrNode node : block.getNodes()) {
				mapping.put(node, cfa.createLoc());
			}

			// Branch nodes need a separate location on their own
			if (block.getTerminator() instanceof JumpIfNode || block.getTerminator() instanceof BranchTableNode) {
				mapping.put(block.getTerminator(), cfa.createLoc());
			}
		}

		IrNode firstNode = func.getEntryNode().getTarget().getNodeByIndex(0);

		// Replace the initial node
		cfa.removeLoc(mapping.get(firstNode));
		mapping.put(firstNode, cfa.getInitLoc());
		mapping.put(func.getExitNode(), cfa.getFinalLoc());

		/*
		 * Create the CFA edges
		 *
		 * Nodes inside a block are sequential, so they just need to be linked together.
		 * Terminator nodes' targets need to be replaced by their block's first node.
		 */
		for (BasicBlock block : func.getBlocksDFS()) {
			List<NonTerminatorIrNode> nodes = block.getNodes();
			int i;
			for (i = 0; i < nodes.size() - 1; i++) { // Skip the last node (the terminator), it will be handled out of the loop
				IrNode node = nodes.get(i);

				CfaLoc source = mapping.get(node);
				CfaLoc target = mapping.get(nodes.get(i + 1));
				createCfaEdge(cfa, node, source, target);
			}

			TerminatorIrNode terminator = block.getTerminator();

			CfaLoc jumpSource;
			if (block.countNodes() != 0) { // There were nonterminators in the block
				IrNode last = nodes.get(i);
				jumpSource = mapping.get(last);
				if (terminator instanceof GotoNode) {
					CfaLoc jumpTarget = mapping.get(((GotoNode) terminator).getTarget().getNodeByIndex(0));
					createCfaEdge(cfa, last, jumpSource, jumpTarget);
				} else if (terminator instanceof JumpIfNode) {
					CfaLoc branchLoc = handleBranch(cfa, mapping, terminator);
					// Create the last -> branch node edge.
					// This will also annotate the edge with the statement corrseponding to the last instruction node
					createCfaEdge(cfa, last, jumpSource, branchLoc);
				} else if (terminator instanceof BranchTableNode) {
					CfaLoc branchLoc = handleBranchTable(cfa, mapping, terminator);
					// Create the last -> branch node edge.
					// This will also annotate the edge with the statement corrseponding to the last instruction node
					createCfaEdge(cfa, last, jumpSource, branchLoc);
				} else if (terminator instanceof ReturnNode) {
					createCfaEdge(cfa, last, jumpSource, cfa.getFinalLoc());
				}
			} else {
				if (terminator instanceof JumpIfNode) {
					handleBranch(cfa, mapping, terminator);
				} else if (terminator instanceof BranchTableNode) {
					handleBranchTable(cfa, mapping, terminator);
				} else if (!(terminator instanceof EntryNode) && !(terminator instanceof ExitNode)) {
					// The goto case should be impossible for normalized CFGs, as they cannot have a block with a single goto node
					throw new RuntimeException(String.format(
						"Invalid terminator class (%s) found in block '%s'. The input function is possibly not normalized.",
						terminator.getClass().getName(),
						block.getName()
					));
				}
			}
		}

		return cfa;
	}

	private static CfaLoc handleBranchTable(MutableCfa cfa, Map<IrNode, CfaLoc> mapping, TerminatorIrNode terminator) {
		BranchTableNode branch = (BranchTableNode) terminator;
		CfaLoc branchLoc = mapping.get(branch);
		List<Expr<? extends BoolType>> conditions = new ArrayList<>();

		for (BranchTableEntry entry : branch.getValueEntries()) {
			Expr<? extends BoolType> cond = Exprs.Eq(branch.getCondition(), entry.getValue());
			conditions.add(cond);

			CfaLoc target = mapping.get(entry.getTarget().getNodeByIndex(0));

			CfaEdge edge = cfa.createEdge(branchLoc, target);
			edge.getStmts().add(Stmts.Assume(cond));
		}

		// Create the edge to the default target
		Expr<? extends BoolType> defaultCond = Exprs.Not(Exprs.Or(conditions));
		CfaLoc defaultTarget = mapping.get(branch.getDefaultTarget().getNodeByIndex(0));

		CfaEdge edge = cfa.createEdge(branchLoc, defaultTarget);
		edge.getStmts().add(Stmts.Assume(defaultCond));
		return branchLoc;
	}

	private static CfaLoc handleBranch(MutableCfa cfa, Map<IrNode, CfaLoc> mapping, TerminatorIrNode terminator) {
		JumpIfNode branch = (JumpIfNode) terminator;
		CfaLoc branchLoc = mapping.get(branch);

		// Jump to the location corresponding to the first node in each branch
		CfaLoc then = mapping.get(branch.getThenTarget().getNodeByIndex(0));
		CfaLoc elze = mapping.get(branch.getElseTarget().getNodeByIndex(0));

		// Add the then and else edges with the required Assume statements
		CfaEdge thenEdge = cfa.createEdge(branchLoc, then);
		thenEdge.getStmts().add(Stmts.Assume(branch.getCondition()));

		CfaEdge elzeEdge = cfa.createEdge(branchLoc, elze);
		elzeEdge.getStmts().add(Stmts.Assume(Exprs.Not(branch.getCondition())));
		return branchLoc;
	}

	/**
	 * Appends a new edge into the CFA
	 *
	 * @param cfa		The CFA to append into
	 * @param node		The instruction node of the source
	 * @param source	The source location
	 * @param target	The target location
	 *
	 * @return A newly created source -> target edge in the CFA
	 */
	private static CfaEdge createCfaEdge(MutableCfa cfa, IrNode node, CfaLoc source, CfaLoc target) {
		CfaEdge edge = cfa.createEdge(source, target);

		if (node instanceof AssignNode<?, ?>) {
			AssignNode<? extends Type, ? extends Type> assign = (AssignNode<?, ?>) node;
			edge.getStmts().add(Stmts.Assign(assign.getVar(), ExprUtils.cast(assign.getExpr(), assign.getVar().getType().getClass())));
		} else if (node instanceof AssertNode) {
			AssertNode assrt = (AssertNode) node;
			edge.getStmts().add(Stmts.Assume(assrt.getCond()));

			CfaEdge errorEdge = cfa.createEdge(source, cfa.getErrorLoc());
			errorEdge.getStmts().add(Stmts.Assume(Exprs.Not(assrt.getCond())));
		}

		return edge;
	}

}
