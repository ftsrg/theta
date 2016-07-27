package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.Collection;
import java.util.Collections;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public class ExitBlock extends BasicBlock {

	public ExitBlock() {
		super("exit", Collections.emptyList());
	}

	@Override
	public Collection<? extends BasicBlock> children() {
		return Collections.emptyList();
	}

	@Override
	public TerminatorIrNode getTerminator() {
		return null;
	}

	@Override
	public String getLabel() {
		return "END";
	}

}
