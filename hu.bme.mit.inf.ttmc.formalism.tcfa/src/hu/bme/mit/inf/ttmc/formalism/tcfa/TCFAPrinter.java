package hu.bme.mit.inf.ttmc.formalism.tcfa;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class TCFAPrinter {

	private TCFAPrinter() {
	}

	public static String toGraphvizSting(final TCFA tcfa) {
		final Map<TCFALoc, Integer> ids = createIds(tcfa);
		final StringBuilder sb = new StringBuilder();

		sb.append("digraph tcfa {\n");
		for (final TCFALoc loc : tcfa.getLocs()) {
			sb.append(toGraphvizString(tcfa, loc, ids));
		}

		for (final TCFAEdge edge : tcfa.getEdges()) {
			sb.append(toGraphvizString(tcfa, edge, ids));
		}

		sb.append("}");
		return sb.toString();
	}

	private static Map<TCFALoc, Integer> createIds(final TCFA tcfa) {
		final Map<TCFALoc, Integer> ids = new HashMap<>();
		int id = 0;
		for (final TCFALoc loc : tcfa.getLocs()) {
			ids.put(loc, id);
			id++;
		}
		return ids;
	}

	private static String toGraphvizString(final TCFA tcfa, final TCFALoc loc, final Map<TCFALoc, Integer> ids) {
		final StringBuilder sb = new StringBuilder();
		sb.append(ids.get(loc));
		sb.append("[label=\"\\\n");
		sb.append(loc.getName());
		sb.append("\\n\\\n");
		for (final Expr<? extends BoolType> invar : loc.getInvars()) {
			sb.append(invar.toString());
			sb.append("\\n\\\n");
		}
		sb.append("\"]\n");
		return sb.toString();
	}

	private static String toGraphvizString(final TCFA cfa, final TCFAEdge edge, final Map<TCFALoc, Integer> ids) {
		final StringBuilder sb = new StringBuilder();
		sb.append(ids.get(edge.getSource()));
		sb.append(" -> ");
		sb.append(ids.get(edge.getTarget()));
		sb.append("[label=\"\\\n");
		for (final Stmt stmt : edge.getStmts()) {
			sb.append(stmt.toString());
			sb.append("\\n\\\n");
		}
		sb.append("\"]\n");
		return sb.toString();
	}

}
