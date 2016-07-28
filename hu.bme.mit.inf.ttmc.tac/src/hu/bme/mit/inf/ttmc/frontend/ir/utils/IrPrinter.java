package hu.bme.mit.inf.ttmc.frontend.ir.utils;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;

public class IrPrinter {

	public static String toText(Function func) {
		StringBuilder sb = new StringBuilder();

		return sb.toString();
	}

	public static String toGraphvizString(Function func) {
		StringBuilder sb = new StringBuilder();
		sb.append("digraph G {\n");

		for (BasicBlock block : func.getBlocks()) {
			sb.append(String.format("node_%s [label=\"%s\"];\n", block.getName(), block.getLabel()));

			if (block.getTerminator() instanceof JumpIfNode) {
				JumpIfNode terminator = (JumpIfNode) block.getTerminator();
				sb.append(String.format("node_%s -> node_%s [label=\" True\"];\n", block.getName(), terminator.getThenTarget().getName()));
				sb.append(String.format("node_%s -> node_%s [label=\" False\"];\n", block.getName(), terminator.getElseTarget().getName()));
			} else {
				block.children().forEach(s ->
					sb.append(String.format("node_%s -> node_%s;\n", block.getName(), s.getName()))
				);
			}

		}

		sb.append("}\n");

		return sb.toString();
	}

}
