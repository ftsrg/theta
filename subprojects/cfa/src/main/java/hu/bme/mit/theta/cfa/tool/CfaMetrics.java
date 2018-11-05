package hu.bme.mit.theta.cfa.tool;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Edge;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntExprs;

/**
 * A command line tool for getting metrics of a CFA.
 */
public class CfaMetrics {

	public static void main(final String[] args) throws IOException {
		final TableWriter writer = new BasicTableWriter(System.out, ",", "\"", "\"");

		if (args.length == 1 && "--header".equals(args[0])) {
			writer.cell("Model").cell("Vars").cell("BoolVars").cell("IntVars").cell("Locs").cell("Edges")
					.cell("CyclomaticComplexity").cell("Assigns").cell("Assumes").cell("Havocs");
			writer.newRow();
			return;
		}

		final InputStream inputStream = new FileInputStream(args[0]);
		final CFA cfa = CfaDslManager.createCfa(inputStream);
		inputStream.close();

		writer.cell(args[0]);
		writer.cell(cfa.getVars().size());
		writer.cell(cfa.getVars().stream().filter(v -> v.getType().equals(BoolExprs.Bool())).count());
		writer.cell(cfa.getVars().stream().filter(v -> v.getType().equals(IntExprs.Int())).count());
		writer.cell(cfa.getLocs().size());
		writer.cell(cfa.getEdges().size());
		writer.cell(cfa.getEdges().size() - cfa.getLocs().size() + 2 * getComponents(cfa));
		writer.cell(cfa.getEdges().stream().filter(e -> e.getStmt() instanceof AssignStmt).count());
		writer.cell(cfa.getEdges().stream().filter(e -> e.getStmt() instanceof AssumeStmt).count());
		writer.cell(cfa.getEdges().stream().filter(e -> e.getStmt() instanceof HavocStmt).count());
		writer.newRow();
	}

	public static int getComponents(final CFA cfa) {
		final Set<CFA.Loc> visited = new HashSet<>();
		int components = 0;

		for (final Loc loc : cfa.getLocs()) {
			if (!visited.contains(loc)) {
				components++;
				visited.add(loc);
				final Queue<Loc> queue = new LinkedList<>();
				queue.add(loc);
				while (!queue.isEmpty()) {
					final Loc next = queue.remove();
					for (final Edge edge : next.getOutEdges()) {
						if (!visited.contains(edge.getTarget())) {
							visited.add(edge.getTarget());
							queue.add(edge.getTarget());
						}
					}
				}
			}
		}

		return components;

	}

}
