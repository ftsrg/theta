package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public class BasicBlockBuilder {

	private List<NonTerminatorIrNode> nodes = new ArrayList<>();
	private TerminatorIrNode terminator;
	private boolean isTerminated = false;
	private String name;

	public BasicBlockBuilder(String name) {
		this.name = name;
	}

	public void addNode(NonTerminatorIrNode node) {
		if (this.isTerminated)
			throw new RuntimeException("Cannot append nodes to terminated blocks.");

		this.nodes.add(node);
	}

	public void terminate(TerminatorIrNode node) {
		if (this.isTerminated)
			throw new RuntimeException("Cannot terminate an already terminated block.");

		this.terminator = node;
		this.isTerminated = true;
	}

	public BasicBlock createBlock() {
		if (!this.isTerminated)
			throw new RuntimeException("The block is not yet terminated.");

		if (this.terminator instanceof GotoNode) {
			GotoNode term = (GotoNode) this.terminator;
			SimpleBasicBlock bb = new SimpleBasicBlock(this.name, this.nodes, term);
			term.getTarget().addParent(bb);

			return bb;
		}

		if (this.terminator instanceof JumpIfNode) {
			JumpIfNode term = (JumpIfNode) this.terminator;
			BranchingBasicBlock bb = new BranchingBasicBlock(this.name, this.nodes, term);
			term.getThenTarget().addParent(bb);
			term.getElseTarget().addParent(bb);

			return bb;
		}

		throw new RuntimeException("Unsupported terminator node.");
	}

}
