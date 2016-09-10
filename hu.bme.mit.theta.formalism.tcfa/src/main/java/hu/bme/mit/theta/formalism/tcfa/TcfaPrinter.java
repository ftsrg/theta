package hu.bme.mit.theta.formalism.tcfa;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.stmt.Stmt;

public class TcfaPrinter {

	private TcfaPrinter() {
	}

	public static String toGraphvizString(final TCFA tcfa) {

		final StringBuilder sb = new StringBuilder();

		sb.append("digraph tcfa {\n");

		final Map<TcfaLoc, Integer> ids = new HashMap<>();
		final TcfaLoc initLoc = tcfa.getInitLoc();
		traverse(sb, initLoc, ids);

		sb.append("}");
		return sb.toString();
	}

	private static void traverse(final StringBuilder sb, final TcfaLoc loc, final Map<TcfaLoc, Integer> ids) {
		if (!ids.containsKey(loc)) {
			ids.put(loc, ids.size());
			sb.append(toGraphvizString(loc, ids));
			for (final TcfaEdge outEdge : loc.getOutEdges()) {
				final TcfaLoc target = outEdge.getTarget();
				traverse(sb, target, ids);
				sb.append(toGraphvizString(outEdge, ids));
			}
		}
	}

	private static String toGraphvizString(final TcfaLoc loc, final Map<TcfaLoc, Integer> ids) {
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

	private static String toGraphvizString(final TcfaEdge edge, final Map<TcfaLoc, Integer> ids) {
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
