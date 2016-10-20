package hu.bme.mit.inf.theta.benchmark.bmc;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Queue;
import java.util.Stack;
import java.util.function.Function;
import java.util.stream.Collectors;

import javax.management.Query;

import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.inf.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.theta.formalism.utils.StmtUnroller;
import hu.bme.mit.inf.theta.formalism.utils.StmtUnroller.StmtToExprResult;
import hu.bme.mit.inf.theta.formalism.utils.VarIndexes;
import hu.bme.mit.inf.theta.solver.Solver;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.SolverStatus;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

public class BoundedModelChecker {

	public enum CheckResult {
		CHECK_FAILED, CHECK_PASSED, CHECK_UNKNOWN, CHECK_INTERNAL_ERROR, CHECK_TIMEOUT
	}

	public enum BmcResult {
		BMC_CONTINUE, BMC_CHECK_FAILED, BMC_NO_PATH, BMC_LIMIT_REACHED
	}

	private class SearchTreeNode {

		private final int depth;
		private final SearchTreeNode parent;
		private final CfaLoc loc;
		private final List<Stmt> stmts;

		public SearchTreeNode(int depth, SearchTreeNode parent, CfaLoc loc, List<Stmt> stmts) {
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

	private Logger log;

	public BoundedModelChecker(Logger log) {
		this.log = log;
	}

	public CheckResult checkAll(Collection<CFA> cfas, int k) {
		for (CFA cfa : cfas) {
			this.log.writeln("Checking a CFA slice...", 6);
			if (this.check(cfa, k) == CheckResult.CHECK_FAILED)
				return CheckResult.CHECK_FAILED;

			this.log.writeln("No errors found in current CFA, moving on to the next or aborting...", 6);
		}

		this.log.writeln("Check finished.", 6);
		return CheckResult.CHECK_UNKNOWN;
	}

	public CheckResult checkAll(Collection<CFA> cfas, Function<CFA, Integer> kHeur) {
		for (CFA cfa : cfas) {
			int k = kHeur.apply(cfa);
			this.log.writeln("Checking with k=" + k, 6);

			if (this.check(cfa, k) == CheckResult.CHECK_FAILED)
				return CheckResult.CHECK_FAILED;
		}

		return CheckResult.CHECK_UNKNOWN;
	}

	public CheckResult check(CFA cfa, int k) {
		SolverManager manager = new Z3SolverManager();
		Solver solver = manager.createSolver(true, true);

		CfaLoc init = cfa.getInitLoc();
		CfaLoc error = cfa.getErrorLoc();

		VarIndexes.Builder viBuilder = VarIndexes.builder(1);
		VarIndexes vi = viBuilder.build();

		Queue<SearchTreeNode> queue = new ArrayDeque<>();
		queue.add(new SearchTreeNode(0, null, init, Collections.emptyList())); // add the initial node

		while (!queue.isEmpty()) {
			SearchTreeNode node = queue.poll();

			if (node == error) {
				this.log.writeln("Found an error path with the length of " + node.getDepth(), 6);

				List<Stmt> stmts = this.getNodeStatements(node);
				StmtToExprResult exprs = StmtUnroller.transform(stmts, vi);
				vi = exprs.getIndexes();

				solver.push();
				solver.add(exprs.getExprs());

				SolverStatus status = solver.check();
				if (status == SolverStatus.SAT) {
					this.log.writeln("Solver found a solution, check FAILED.", 1);
					return CheckResult.CHECK_FAILED;
				}

				solver.pop();
			} else if (node.getDepth() < k) {
				for (CfaEdge edge : node.getLoc().getOutEdges()) {
					CfaLoc loc = edge.getTarget();
					List<Stmt> stmts = edge.getStmts();

					SearchTreeNode stn = new SearchTreeNode(node.getDepth() + 1, node, loc, stmts);
					queue.add(stn);
				}
			}
		}

		return CheckResult.CHECK_UNKNOWN;
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

	private BmcResult search(CfaLoc from, CfaLoc target, int depth, int k, Solver solver, VarIndexes vi,
			List<CfaLoc> avoid) {
		// this.log.writeln("Searching in depth of " + depth, 7, 1);
		if (depth == k)
			return BmcResult.BMC_LIMIT_REACHED;

		for (CfaEdge out : from.getOutEdges()) {
			solver.push();
			StmtToExprResult res = StmtUnroller.transform(out.getStmts(), vi);
			CfaLoc child = out.getTarget();

			solver.add(res.getExprs());
			// this.log.writeln("Current asserts: " +
			// solver.getAssertions().toString(), 7, 2);

			if (child == target) {
				this.log.writeln("Found an error path with the length of " + depth, 6);
				solver.getAssertions().forEach(a -> {
					this.log.writeln("Clause: " + a.toString(), 7, 1);
				});

				this.log.writeln("Running solver...", 7);
				SolverStatus status = solver.check();
				this.log.writeln("Solver finished, status: " + status.toString(), 7);
				if (status == SolverStatus.SAT) {
					this.log.writeln("Solver found a solution, check FAILED", 7);
					return BmcResult.BMC_CHECK_FAILED;
				}
			} else if (!avoid.contains(child)) {
				BmcResult bmcRes = this.search(child, target, depth + 1, k, solver, res.getIndexes(), avoid);
				switch (bmcRes) {
				case BMC_CHECK_FAILED:
					return BmcResult.BMC_CHECK_FAILED;
				case BMC_LIMIT_REACHED:
					avoid.add(child);
					break;
				case BMC_CONTINUE:
					break;
				case BMC_NO_PATH:
					break;
				default:
					break;
				}
			}

			solver.pop();
		}

		if (from.getOutEdges().size() == 0) {
			this.log.writeln("No path was found.", 7);
			// avoid.add(from);
			return BmcResult.BMC_NO_PATH;
		}

		return BmcResult.BMC_CONTINUE;
	}

	/*
	 * private BmcResult search(CfaLoc node, CfaLoc target, Solver solver,
	 * Queue<CfaEdge> queue, VarIndexes vi, int depth, int k) {
	 * System.out.println("K=" + depth); if (depth == 0) return
	 * BmcResult.BMC_CONTINUE;
	 *
	 * solver.push(); for (CfaEdge edge : node.getOutEdges()) { CfaLoc child =
	 * edge.getTarget();
	 *
	 * solver.push();
	 *
	 * StmtToExprResult res = StmtUnroller.transform(edge.getStmts(), vi);
	 * solver.add(res.getExprs());
	 *
	 * if (child == target) { this.log.writeln(
	 * "Found an error path with the length of " + depth, 6);
	 *
	 * solver.getAssertions().forEach(t -> { this.log.writeln("Clause: " + t, 7,
	 * 1); });
	 *
	 * this.log.writeln("Running solver...", 7); SolverStatus status =
	 * solver.check(); this.log.writeln("Solver finished running, status: " +
	 * status.toString(), 7); if (status == SolverStatus.SAT) {
	 * this.log.writeln("Solver found a solution. Check failed.", 7);
	 *
	 * return BmcResult.BMC_CHECK_FAILED; } } else { }
	 *
	 * solver.pop(); } solver.pop();
	 *
	 *
	 * return BmcResult.BMC_NO_PATH; }
	 *
	 * private BmcResult find(CfaLoc node, CfaLoc target, Solver solver,
	 * VarIndexes vi, int depth) { if (depth == 0) return
	 * BmcResult.BMC_LIMIT_REACHED;
	 *
	 * for (CfaEdge edge : node.getOutEdges()) { CfaLoc parent =
	 * edge.getTarget();
	 *
	 * solver.push();
	 *
	 * StmtToExprResult res = StmtUnroller.transform(edge.getStmts(), vi);
	 * solver.add(res.getExprs());
	 *
	 * if (parent == target) { this.log.writeln(
	 * "Found an error path with the length of " + depth, 6);
	 *
	 * solver.getAssertions().forEach(t -> { this.log.writeln("Clause: " + t, 7,
	 * 1); });
	 *
	 * this.log.writeln("Running solver...", 7); SolverStatus status =
	 * solver.check(); this.log.writeln("Solver finished running, status: " +
	 * status.toString(), 7); if (status == SolverStatus.SAT) {
	 * this.log.writeln("Solver found a solution. Check failed.", 7);
	 *
	 * return BmcResult.BMC_CHECK_FAILED; } }
	 *
	 * BmcResult subRes = find(parent, target, solver, res.getIndexes(), depth -
	 * 1);
	 *
	 *
	 * if (subRes == BmcResult.BMC_CHECK_FAILED) return
	 * BmcResult.BMC_CHECK_FAILED;
	 *
	 * solver.pop(); }
	 *
	 * return BmcResult.BMC_NO_PATH; }
	 */
	/*
	 * public CheckResult check(CFA cfa, int k) { SolverManager manager = new
	 * Z3SolverManager(); Solver solver = manager.createSolver(true, true);
	 *
	 * VarIndexes.Builder viBuilder = VarIndexes.builder(1); VarIndexes vi =
	 * viBuilder.build();
	 *
	 * for (int i = 0; i < k; i++) { List<List<CfaEdge>> paths = new
	 * ArrayList<>();
	 *
	 * this.search(cfa.getInitLoc(), cfa.getErrorLoc(), i, new Stack<>(),
	 * paths);
	 *
	 * if (!paths.isEmpty()) { // there is an error path for (List<CfaEdge> path
	 * : paths) { solver.push(); this.log.writeln(
	 * "Found an error path with length of " + i, 6);
	 *
	 * for (CfaEdge edge : path) { for (Stmt stmt : edge.getStmts()) {
	 * StmtToExprResult result = StmtUnroller.transform(stmt, vi); vi =
	 * result.getIndexes();
	 *
	 * result.getExprs().forEach(expr -> { this.log.writeln("Clause: " +
	 * expr.toString(), 7, 0); solver.add(expr); }); } }
	 *
	 * this.log.writeln("Starting SAT check", 7); SolverStatus status =
	 * solver.check(); if (status == SolverStatus.SAT) { this.log.writeln(
	 * "Check FAILED, system model:", 0);
	 * this.log.writeln(solver.getModel().toString(), 0, 1);
	 *
	 * return CheckResult.CHECK_FAILED; } else if (status ==
	 * SolverStatus.UNKNOWN) { this.log.writeln(
	 * "Check UNKNOWN, system assertions:", 5);
	 * this.log.writeln(solver.getAssertions().toString(), 5); }
	 * this.log.writeln("SAT check done", 7); solver.pop(); } } }
	 *
	 * return CheckResult.CHECK_PASSED; }
	 */

	private boolean search(CfaLoc node, CfaLoc target, int depth, Stack<CfaEdge> path, List<List<CfaEdge>> paths) {
		if (depth == 0 && node == target) {
			return true;
		}

		if (depth > 0) {
			for (CfaEdge out : node.getOutEdges()) {
				path.push(out);
				if (true == search(out.getTarget(), target, depth - 1, path, paths)) { // Found
																						// it
					paths.add(new ArrayList<>(path));
				}

				path.pop();
			}
		}

		return false;
	}

}
