package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.TerminatorIrNode;

public class InstructionBuilder {

	private final Map<String, BasicBlock> blocks = new HashMap<>();
	private final Stack<BasicBlock> insertPoints = new Stack<>();

	private BasicBlock insertPoint;

	private Function function;

	public InstructionBuilder(Function function) {
		this.function = function;
	}

	public void insertNode(NonTerminatorIrNode node) {
		this.insertPoint.addNode(node);
	}

	public BasicBlock createBlock(String name) {
		String bname = name;
		int blockId = 0;
		while (this.blocks.containsKey(bname)) {
			bname = name + blockId++;
		}

		BasicBlock bb = this.function.createBlock(bname);
		this.blocks.put(bname, bb);

		return bb;
	}

	public BasicBlock getInsertPoint() {
		return this.insertPoint;
	}

	public void setInsertPoint(BasicBlock block) {
		this.insertPoint = block;
	}

	public void pushInsertPoint(BasicBlock block) {
		this.insertPoints.push(block);
	}

	public void popInsertPoint() {
		this.insertPoints.pop();
	}

	public void terminateInsertPoint(TerminatorIrNode terminator) {
		this.insertPoint.terminate(terminator);
	}

	public BasicBlock getExitBlock() {
		return this.function.getExitBlock();
	}


}
