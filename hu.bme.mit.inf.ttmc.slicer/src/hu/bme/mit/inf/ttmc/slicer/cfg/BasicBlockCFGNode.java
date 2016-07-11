package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class BasicBlockCFGNode extends CFGNode {

	private List<Stmt> block;

	public BasicBlockCFGNode(List<Stmt> block) {
		this.block = block;
	}

	public List<Stmt> getStmts()
	{
		return this.block;
	}

	public Collection<BasicBlockCFGNode> getBlockParents() {
		return this.getParents().stream().filter(s -> s instanceof BasicBlockCFGNode).map(s -> (BasicBlockCFGNode) s).collect(Collectors.toSet());
	}

	@Override
	public String getLabel() {
		StringBuilder sb = new StringBuilder();
		this.block.forEach(s -> sb.append(s + "\\n"));
		return sb.toString();
	}

	@Override
	public String toString() {
		return this.getLabel();
	}

	@Override
	public CFGNode copy() {
		return new BasicBlockCFGNode(this.block);
	}

}
