package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;

public class SimpleBasicBlock extends BasicBlock {

	private GotoNode terminator;

	public SimpleBasicBlock(String name, List<NonTerminatorIrNode> nodes, GotoNode terminator) {
		super(name, nodes);
		this.terminator = terminator;
	}

	@Override
	public Collection<? extends BasicBlock> children() {
		return Collections.singletonList(this.terminator.getTarget());
	}

	@Override
	public GotoNode  getTerminator() {
		return this.terminator;
	}

}
