package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class CFAPrinter {

	private CFAPrinter() {

	}

	public static String toGraphvizSting(final CFA cfa) {
		final Map<CFALoc, String> labels = createLocLabels(cfa);
		final StringBuilder sb = new StringBuilder();

		sb.append("digraph cfa {\n");
		sb.append("edge [fontname = \"courier\"]\n");
		for (final CFALoc loc : cfa.getLocs()) {
			sb.append(toGraphvizString(cfa, loc, labels));
		}

		for (final CFAEdge edge : cfa.getEdges()) {
			sb.append(toGraphvizString(cfa, edge, labels));
		}

		sb.append("}");
		return sb.toString();
	}

	private static Map<CFALoc, String> createLocLabels(final CFA cfa) {
		final Map<CFALoc, String> labels = new HashMap<>();
		int id = 0;
		for (final CFALoc loc : cfa.getLocs()) {
			if (loc == cfa.getInitLoc()) {
				labels.put(loc, "begin");
			} else if (loc == cfa.getFinalLoc()) {
				labels.put(loc, "end");
			} else if (loc == cfa.getErrorLoc()) {
				labels.put(loc, "error");
			} else {
				labels.put(loc, Integer.toString(id));
				id++;
			}
		}
		return labels;
	}

	private static String toGraphvizString(final CFA cfa, final CFALoc loc, final Map<CFALoc, String> labels) {
		final StringBuilder sb = new StringBuilder();
		sb.append(labels.get(loc));

		if (loc == cfa.getErrorLoc()) {
			sb.append(" [peripheries=2]");
		}

		sb.append("\n");
		return sb.toString();
	}

	private static String toGraphvizString(final CFA cfa, final CFAEdge edge, final Map<CFALoc, String> labels) {
		final StringBuilder sb = new StringBuilder();
		sb.append(labels.get(edge.getSource()));
		sb.append(" -> ");
		sb.append(labels.get(edge.getTarget()));
		sb.append("[label=\"\\\n");
		for (final Stmt stmt : edge.getStmts()) {
			sb.append(stmt.toString());
			sb.append("\\n\\\n");
		}
		sb.append("\"]\n");
		return sb.toString();
	}

}
