package hu.bme.mit.inf.ttmc.frontend.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class ExitNode implements TerminatorIrNode {

	@Override
	public String getLabel() {
		return "exit";
	}

	@Override
	public List<BasicBlock> getTargets() {
		return Collections.emptyList();
	}

}
