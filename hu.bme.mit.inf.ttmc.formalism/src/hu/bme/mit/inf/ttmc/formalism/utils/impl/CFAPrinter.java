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
		final Map<CFALoc, Integer> ids = createIds(cfa);
		final StringBuilder sb = new StringBuilder();
		
		sb.append("digraph cfa {\n");
		sb.append("edge [fontname = \"courier\"]\n");
		for (CFALoc loc : cfa.getLocs()) {
			sb.append(toGraphvizString(cfa, loc, ids));
		}
		
		for (CFAEdge edge : cfa.getEdges()) {
			sb.append(toGraphvizString(cfa, edge, ids));
		}
		
		sb.append("}");
		return sb.toString();
	}
	
	private static Map<CFALoc, Integer> createIds(final CFA cfa) {
		final Map<CFALoc, Integer> ids = new HashMap<>();
		int id = 0;
		for (final CFALoc loc : cfa.getLocs()) {
			ids.put(loc, id);
			id++;
		}
		return ids;
	}
	
	private static String toGraphvizString(final CFA cfa, final CFALoc loc, final Map<CFALoc, Integer> ids) {
		final StringBuilder sb = new StringBuilder();
		sb.append(ids.get(loc));
		if (loc == cfa.getErrorLoc()) {
			sb.append(" [peripheries=2]");
		}
		sb.append("\n");
		return sb.toString();
	}
	
	private static String toGraphvizString(final CFA cfa, final CFAEdge edge, final Map<CFALoc, Integer> ids) {
		final StringBuilder sb = new StringBuilder();
		sb.append(ids.get(edge.getSource()));
		sb.append(" -> ");
		sb.append(ids.get(edge.getTarget()));
		sb.append("[label=\"\\\n");
		for (Stmt stmt : edge.getStmts()) {
			sb.append(stmt.toString());
			sb.append("\\n\\\n");
		}
		sb.append("\"]\n");
		return sb.toString();
	}
	
}
