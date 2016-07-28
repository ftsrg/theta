package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.node.ExitNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;

public class Function {

	private final String name;
	private final Type type;
	private final List<VarDecl<? extends Type>> locals = new ArrayList<>();
	private final Map<String, BasicBlock> blocks = new HashMap<>();

	private BasicBlock entry;
	private BasicBlock exit;

	public Function(String name, Type type) {
		this.name = name;
		this.type = type;

		this.exit = new BasicBlock(name + "_exit", this);
		this.exit.terminate(new ExitNode());
	}

	public void addLocalVariable(VarDecl<? extends Type> variable) {
		this.locals.add(variable);
	}

	public void addBasicBlock(BasicBlock block) {
		this.blocks.put(block.getName(), block);
	}

	public Collection<BasicBlock> getBlocks() {
		return this.blocks.values();
	}

	public String getName() {
		return this.name;
	}

	public void setEntryBlock(BasicBlock entry) {
		this.entry = entry;
		this.addBasicBlock(entry);
	}

	public BasicBlock getEntryBlock() {
		return this.entry;
	}

	public void setExitBlock(BasicBlock exit) {
		this.exit = exit;
	}

	public BasicBlock getExitBlock() {
		return this.exit;
	}


}
