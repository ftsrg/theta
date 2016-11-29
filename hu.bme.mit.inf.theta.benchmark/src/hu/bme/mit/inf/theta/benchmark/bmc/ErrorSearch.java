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

		Queue<SearchTreeNode> revQueue = new ArrayDeque<>();
		revQueue.add(new SearchTreeNode(0, null, this.error(), Collections.emptyList()));

		while (k < max) {
			this.log.writeln("Checking forward direction with bound of k=" + k, 7);
			Queue<SearchTreeNode> newQueue = new ArrayDeque<>();

			/*
			 * Check the forward direction.
			 *
			 * If we are able to find an error path with the length of k, we need to check its feasibility.
			 * If the error path is feasible, we can terminate the error search and return a counter-example.
			 */
			while (!queue.isEmpty()) {
				SearchTreeNode node = queue.poll();
				int depth = node.getDepth();

				if (node.getLoc() == this.error()) {
					this.solver.push();

					List<Stmt> stmts = this.getNodeStatements(node);

					StmtToExprResult exprs = StmtUnroller.transform(stmts, this.vi);
					this.solver.add(exprs.getExprs());

					this.log.writeln("Found an error path with the length of " + k, 6);
					this.log.writeln("Running solver...", 6);
					this.solver.check();
					if (this.solver.getStatus() == SolverStatus.SAT) {
						this.log.writeln("Solver found a solution, check FAILED.", 1, 1);
						this.log.writeln("System model: " + solver.getModel().toString(), 2, 1);

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

			this.log.writeln("Checking backwards direction...", 6);
			Queue<SearchTreeNode> newRevQueue = new ArrayDeque<>();

			/*
			 * Check the backwards direction.
			 *
			 * For every added node we need to check its feasibility.
			 * If a path is feasible, then we can terminate the backwards search and increase the bound.
			 * If no feasible path was found, then we can terminate the search and return a passed check.
			 */
			boolean revRes = true;
			while (!revQueue.isEmpty()) {
				SearchTreeNode node = revQueue.poll();
				int depth = node.getDepth();

				// Check whether this is error path is possible
				this.solver.push();

				List<Stmt> stmts = this.getNodeStatements(node);
				Collections.reverse(stmts);

				StmtToExprResult exprs = StmtUnroller.transform(stmts, this.vi);
				this.solver.add(exprs.getExprs());

				this.log.writeln("Backwards assertions: " + solver.getAssertions().toString(), 7, 1);

				this.log.writeln("Running backwards solver...", 6, 1);
				this.solver.check();
				if (this.solver.getStatus() == SolverStatus.SAT) {
					this.log.writeln("Solver found a solution, failure is possible.", 6, 1);
					this.log.writeln("System model: " + solver.getModel().toString(), 7, 1);

					revRes = false;
					revQueue.addAll(this.getParentNodes(node));

					this.solver.pop();
					break;
				}

				this.log.writeln("Solver finished, status: " + solver.getStatus(), 6, 1);
				this.solver.pop();

				// Add this node's children to the search tree
				if (depth + 1 < k) {
					revQueue.addAll(this.getParentNodes(node));
				} else {
					// These nodes cannot be added now because they would cause an infinite loop
					newRevQueue.addAll(this.getParentNodes(node));
				}
			}

			if (revRes) {
				this.log.writeln("No forward or backward error paths were found, check PASSED.", 1);
				return CheckResult.CHECK_PASSED;
			} else {
				this.log.writeln("Increasing bound to " + (k + 1), 5);
				k = k + 1;
				queue = newQueue;
				revQueue.addAll(newRevQueue);
			}

		}

		this.log.writeln("Maximum bound reached, cannot continue. Check result is UNKNOWN.", 1);
		return CheckResult.CHECK_UNKNOWN;
	}

	private List<SearchTreeNode> getParentNodes(SearchTreeNode node) {
		List<SearchTreeNode> children = new ArrayList<>();

		for (CfaEdge edge : node.getLoc().getInEdges()) {
			CfaLoc loc = edge.getSource();
			List<Stmt> stmts = edge.getStmts();
			int d2 = node.getDepth() + 1;

			SearchTreeNode stn = new SearchTreeNode(d2, node, loc, stmts);
			children.add(stn);
		}

		return children;
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
