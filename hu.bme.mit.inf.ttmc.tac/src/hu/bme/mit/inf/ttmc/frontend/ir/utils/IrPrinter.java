package hu.bme.mit.inf.ttmc.frontend.ir.utils;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.BranchingBasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;

public class IrPrinter {

	public static String toText(Function func) {
		StringBuilder sb = new StringBuilder();

		BasicBlock current = func.getEntryBlock();
		while (true) {
			sb.append(current.getName() + ":\n");
			for (IrNode node : current.getNodes()) {
				sb.append("   " + node.getLabel() + "\n");
			}

			if (current.getTerminator() == null) {
				sb.append("   END\n");
				break;
			}

			sb.append("   " + current.getTerminator().getLabel() + "\n");
			current = current.getTerminator().getDefaultTarget();
		};

		return sb.toString();
	}

	public static String toGraphvizString(Function func) {
		StringBuilder sb = new StringBuilder();
		sb.append("digraph G {\n");
		sb.append("node [shape=\"record\"];\n");

		for (BasicBlock block : func.getBlocks()) {
			if (block instanceof BranchingBasicBlock) {
				sb.append(String.format("node_%s [label=\"{%s|{<s0>True|<s1>False}}\"];\n", block.getName(), block.getLabel()));
				sb.append(String.format("node_%s -> node_%s;\n", block.getName(), ((BranchingBasicBlock) block).getThenBranch().getName()));
				sb.append(String.format("node_%s -> node_%s;\n", block.getName(), ((BranchingBasicBlock) block).getElseBranch().getName()));
			} else {
				sb.append(String.format("node_%s [label=\"{%s}\"];\n", block.getName(), block.getLabel()));
				block.children().forEach(s ->
					sb.append(String.format("node_%s -> node_%s;\n", block.getName(), s.getName()))
				);

			}

		}

		sb.append("}\n");

		return sb.toString();
	}

}
