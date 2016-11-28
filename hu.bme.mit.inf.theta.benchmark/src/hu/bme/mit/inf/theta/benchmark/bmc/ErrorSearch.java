package hu.bme.mit.inf.theta.benchmark.bmc;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.TimeUnit;

import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker.CheckResult;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.inf.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.theta.formalism.utils.StmtUnroller;
import hu.bme.mit.inf.theta.formalism.utils.VarIndexes;
import hu.bme.mit.inf.theta.formalism.utils.StmtUnroller.StmtToExprResult;
import hu.bme.mit.inf.theta.solver.Solver;
import hu.bme.mit.inf.theta.solver.SolverStatus;

public class ErrorSearch {

	public enum CheckResult {
		CHECK_FAILED, CHECK_PASSED, CHECK_UNKNOWN, CHECK_INTERNAL_ERROR, CHECK_TIMEOUT
	}

	public static class SearchTreeNode {
		private static long count = 0;
		private final int depth;
		private final SearchTreeNode parent;
		private final CfaLoc loc;
		private final List<Stmt> stmts;

		public SearchTreeNode(int depth, SearchTreeNode parent, CfaLoc loc, List<Stmt> stmts) {
			count++;
			this.depth = depth;
			this.parent = parent;
			this.loc = loc;
			this.stmts = stmts;
		}

		public int getDepth() {
			return depth;
		}

		public SearchTreeNode getParent() {
			return parent;
		}

		public CfaLoc getLoc() {
			return loc;
		}

		public List<Stmt> getStmts() {
			return stmts;
		}
	}

	private final CFA cfa;
	private final Solver solver;
	private final Logger log;
	private VarIndexes vi;

	public ErrorSearch(CFA cfa, Solver solver, Logger log) {
		this.cfa = cfa;
		this.solver = solver;
		this.log = log;
		this.vi = VarIndexes.builder(0).build();
	}

	/**
	 * Performs forward search from the initial node with the maximum depth of max
	 */
	public CheckResult check(final int max) {
		int k = 0;
		Queue<SearchTreeNode> queue = new ArrayDeque<>();
		queue.add(new SearchTreeNode(0, null, this.init(), Collections.emptyList()));

		while (k < max) {
			Queue<SearchTreeNode> newQueue = new ArrayDeque<>();

			while (!queue.isEmpty()) {
				SearchTreeNode node = queue.poll();
				int depth = node.getDepth();

				if (node.getLoc() == this.error()) {
					this.solver.push();

					List<Stmt> stmts = this.getNodeStatements(node);

					StmtToExprResult exprs = StmtUnroller.transform(stmts, this.vi);
					this.solver.add(exprs.getExprs());

					this.log.writeln("Running solver...", 6);
					this.solver.check();
					if (this.solver.getStatus() == SolverStatus.SAT) {
						this.log.writeln("Solver found a solution, check FAILED.", 1);
						this.log.writeln("System model: " + solver.getModel().toString(), 2);

						return CheckResult.CHECK_FAILED;
					}
					this.log.writeln("Solver finished, status: " + solver.getStatus(), 6);

					this.solver.pop();
				} else if (depth + 1 < k) {
					queue.addAll(this.getChildrenNodes(node));
				} else {
					newQueue.addAll(this.getChildrenNodes(node));
				}
			}

			this.log.writeln("Increasing bound to " + (k + 1), 7);
			k = k + 1;
			queue = newQueue;
		}

		return CheckResult.CHECK_UNKNOWN;
	}

	private List<SearchTreeNode> getChildrenNodes(SearchTreeNode node) {
		List<SearchTreeNode> children = new ArrayList<>();

		for (CfaEdge edge : node.getLoc().getOutEdges()) {
			CfaLoc loc = edge.getTarget();
			List<Stmt> stmts = edge.getStmts();
			int d2 = node.getDepth() + 1;

			SearchTreeNode stn = new SearchTreeNode(d2, node, loc, stmts);
			children.add(stn);
		}

		return children;
	}

	private CfaLoc error() {
		return this.cfa.getErrorLoc();
	}

	private CfaLoc init() {
		return this.cfa.getInitLoc();
	}

	private List<Stmt> getNodeStatements(SearchTreeNode node) {
		List<Stmt> stmts = new ArrayList<>();

		SearchTreeNode parent = node;
		while (parent != null) {
			stmts.addAll(0, parent.getStmts());
			parent = parent.getParent();
		}

		return stmts;
	}


}
