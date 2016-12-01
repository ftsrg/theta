package hu.bme.mit.theta.frontend.c.benchmark.utils;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;

public class CfaMeasures {

	private static class CfaSearchTreeNode {
		private CfaLoc loc;
		private CfaSearchTreeNode parent;

		public CfaSearchTreeNode(CfaLoc loc, CfaSearchTreeNode parent) {
			this.loc = loc;
			this.parent = parent;
		}
	}

	public static int dfs(CfaLoc loc, List<CfaLoc> visited, int depth) {
		visited.add(loc);
		int d = depth;

		for (CfaEdge edge : loc.getOutEdges()) {
			CfaLoc child = edge.getTarget();

			if (!visited.contains(child)) {
				int d2 = dfs(child, visited, depth + 1);
				if (d2 > d)
					d = d2;
			}
		}

		return d;
	}

	public static int depth(CFA cfa) {
		return dfs(cfa.getInitLoc(), new ArrayList<>(), 0);
	}

}
