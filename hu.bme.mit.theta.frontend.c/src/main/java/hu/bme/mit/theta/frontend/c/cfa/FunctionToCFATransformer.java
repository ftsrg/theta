package hu.bme.mit.theta.frontend.c.cfa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.stmt.impl.Stmts;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.formalism.cfa.impl.MutableCfa;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.AssertNode;
import hu.bme.mit.theta.frontend.c.ir.node.AssignNode;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode;
import hu.bme.mit.theta.frontend.c.ir.node.BranchTableNode.BranchTableEntry;
import hu.bme.mit.theta.frontend.c.ir.node.EntryNode;
import hu.bme.mit.theta.frontend.c.ir.node.ExitNode;
import hu.bme.mit.theta.frontend.c.ir.node.GotoNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.JumpIfNode;
import hu.bme.mit.theta.frontend.c.ir.node.NonTerminatorIrNode;
import hu.bme.mit.theta.frontend.c.ir.node.ReturnNode;
import hu.bme.mit.theta.frontend.c.ir.node.TerminatorIrNode;

/**
 * A utility class for function to CFA (control flow automata) transformations
 *
 * @author Gyula Sallai <salla016@gmail.com>
 */
public class FunctionToCFATransformer {

	public static CFA createLBE(Function func) {
		return SbeToLbeTransformer.transform(createSBE(func));
	}

	/**
	 * Creates a singe-block encoded CFA from an input function
	 *
	 * @param func
	 *            The function to transform
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

			if (block.getTerminator() instanceof JumpIfNode || block.getTerminator() instanceof BranchTableNode) {
				// Branch nodes need a separate location on their own
				mapping.put(block.getTerminator(), cfa.createLoc());
			} else if (block.countNodes() == 0 && block.getTerminator() instanceof ReturnNode) {
				// If there is a block with a single return terminator without
				// any assignment nodes,
				// we must create a location for this block as well.
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
		 * Nodes inside a block are sequential, so they just need to be linked
		 * together. Terminator nodes' targets need to be replaced by their
		 * block's first node.
		 */
		for (BasicBlock block : func.getBlocksDFS()) {
			List<NonTerminatorIrNode> nodes = block.getNodes();
			int i;
			for (i = 0; i < nodes.size() - 1; i++) { // Skip the last node (the
														// terminator), it will
														// be handled out of the
														// loop
				IrNode node = nodes.get(i);

				CfaLoc source = mapping.get(node);
				CfaLoc target = mapping.get(nodes.get(i + 1));
				createCfaEdge(cfa, node, source, target);
			}

			TerminatorIrNode terminator = block.getTerminator();

			CfaLoc jumpSource;
			if (block.countNodes() != 0) { // There were nonterminators in the
											// block
				IrNode last = nodes.get(i);
				jumpSource = mapping.get(last);
				if (terminator instanceof GotoNode) {
					CfaLoc jumpTarget = mapping.get(((GotoNode) terminator).getTarget().getNodeByIndex(0));
					createCfaEdge(cfa, last, jumpSource, jumpTarget);
				} else if (terminator instanceof JumpIfNode) {
					CfaLoc branchLoc = handleBranch(cfa, mapping, terminator);
					// Create the last -> branch node edge.
					// This will also annotate the edge with the statement
					// corrseponding to the last instruction node
					createCfaEdge(cfa, last, jumpSource, branchLoc);
				} else if (terminator instanceof BranchTableNode) {
					CfaLoc branchLoc = handleBranchTable(cfa, mapping, terminator);
					// Create the last -> branch node edge.
					// This will also annotate the edge with the statement
					// corrseponding to the last instruction node
					createCfaEdge(cfa, last, jumpSource, branchLoc);
				} else if (terminator instanceof ReturnNode) {
					createCfaEdge(cfa, last, jumpSource, cfa.getFinalLoc());
				}
			} else {
				if (terminator instanceof JumpIfNode) {
					handleBranch(cfa, mapping, terminator);
				} else if (terminator instanceof BranchTableNode) {
					handleBranchTable(cfa, mapping, terminator);
				} else if (terminator instanceof ReturnNode) {
					ReturnNode ret = (ReturnNode) terminator;
					CfaLoc retLoc = mapping.get(ret);

					CfaEdge edge = cfa.createEdge(retLoc, cfa.getFinalLoc());
					edge.getStmts().add(Stmts.Return(ret.getExpr()));
				} else if (!(terminator instanceof EntryNode) && !(terminator instanceof ExitNode)) {
					// The goto case should be impossible for normalized CFGs,
					// as they cannot have a block with a single goto node
					throw new RuntimeException(String.format(
							"Invalid terminator class (%s) found in block '%s'. The input function is possibly not normalized.",
							terminator.getClass().getName(), block.getName()));
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
	 * @param cfa
	 *            The CFA to append into
	 * @param node
	 *            The instruction node of the source
	 * @param source
	 *            The source location
	 * @param target
	 *            The target location
	 *
	 * @return A newly created source -> target edge in the CFA
	 */
	private static CfaEdge createCfaEdge(MutableCfa cfa, IrNode node, CfaLoc source, CfaLoc target) {
		CfaEdge edge = cfa.createEdge(source, target);

		if (node instanceof AssignNode<?, ?>) {
			AssignNode<? extends Type, ? extends Type> assign = (AssignNode<?, ?>) node;

			// Procedure calls are not supported in the solver, this workaround
			// assigns
			// an undefined value to each function call results
			if (assign.getExpr() instanceof ProcCallExpr<?>) {
				edge.getStmts().add(Stmts.Havoc(assign.getVar()));
			} else {
				edge.getStmts().add(Stmts.Assign(assign.getVar(),
						ExprUtils.cast(assign.getExpr(), assign.getVar().getType().getClass())));
			}
		} else if (node instanceof AssertNode) {
			AssertNode assrt = (AssertNode) node;
			edge.getStmts().add(Stmts.Assume(assrt.getCond()));

			CfaEdge errorEdge = cfa.createEdge(source, cfa.getErrorLoc());
			errorEdge.getStmts().add(Stmts.Assume(Exprs.Not(assrt.getCond())));
		}

		return edge;
	}

}
