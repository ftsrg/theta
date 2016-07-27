package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;

public class BranchingBasicBlock extends BasicBlock {

	private final JumpIfNode terminator;

	public BranchingBasicBlock(String name, List<NonTerminatorIrNode> nodes, JumpIfNode terminator) {
		super(name, nodes);
		this.terminator = terminator;
	}

	public BasicBlock getThenBranch() {
		return this.terminator.getThenTarget();
	}

	public BasicBlock getElseBranch() {
		return this.terminator.getElseTarget();
	}

	@Override
	public Collection<? extends BasicBlock> children() {
		return Collections.unmodifiableList(
			Arrays.asList(new BasicBlock[]{this.getThenBranch(), this.getElseBranch()})
		);
	}

	@Override
	public JumpIfNode getTerminator() {
		return this.terminator;
	}


}
