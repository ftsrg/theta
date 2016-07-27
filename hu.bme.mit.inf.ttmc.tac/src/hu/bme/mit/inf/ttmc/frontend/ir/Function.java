package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;

public class Function {

	private final String name;
	private final Type type;
	private final List<VarDecl<? extends Type>> locals = new ArrayList<>();
	private final Map<String, BasicBlock> blocks = new HashMap<>();
	private final BasicBlock entry;

	public Function(String name, BasicBlock entry, Type type) {
		this.name = name;
		this.entry = entry;
		this.type = type;
	}

	public void addLocalVariable(VarDecl<? extends Type> variable) {
		this.locals.add(variable);
	}

	public void addBasicBlock(BasicBlock block) {
		this.blocks.put(block.getName(), block);
	}

	public Collection<BasicBlock> getBlocks() {
		List<BasicBlock> blocks = new ArrayList<>();

		BasicBlock current = this.entry;
		while (true) {
			blocks.add(current);

			if (current.getTerminator() == null)
				break;

			current = current.getTerminator().getDefaultTarget();
		}

		return Collections.unmodifiableCollection(blocks);
	}

	public String getName() {
		return this.name;
	}

	public BasicBlock getEntryBlock() {
		return entry;
	}


}
