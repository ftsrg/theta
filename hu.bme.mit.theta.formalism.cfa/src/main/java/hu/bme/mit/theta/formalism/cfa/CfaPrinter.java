package hu.bme.mit.theta.formalism.cfa;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.core.stmt.Stmt;

public class CfaPrinter {

	private CfaPrinter() {

	}

	public static String toGraphvizSting(final CFA cfa) {
		final Map<CfaLoc, String> labels = createLocLabels(cfa);
		final StringBuilder sb = new StringBuilder();

		sb.append("digraph cfa {\n");
		sb.append("edge [fontname = \"courier\"]\n");
		for (final CfaLoc loc : cfa.getLocs()) {
			sb.append(toGraphvizString(cfa, loc, labels));
		}

		for (final CfaEdge edge : cfa.getEdges()) {
			sb.append(toGraphvizString(cfa, edge, labels));
		}

		sb.append("}");
		return sb.toString();
	}

	private static Map<CfaLoc, String> createLocLabels(final CFA cfa) {
		final Map<CfaLoc, String> labels = new HashMap<>();
		int id = 0;
		for (final CfaLoc loc : cfa.getLocs()) {
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

	private static String toGraphvizString(final CFA cfa, final CfaLoc loc, final Map<CfaLoc, String> labels) {
		final StringBuilder sb = new StringBuilder();
		sb.append(labels.get(loc));

		if (loc == cfa.getErrorLoc()) {
			sb.append(" [peripheries=2]");
		}

		sb.append("\n");
		return sb.toString();
	}

	private static String toGraphvizString(final CFA cfa, final CfaEdge edge, final Map<CfaLoc, String> labels) {
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
