package hu.bme.mit.inf.theta.benchmark.bmc;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Queue;
import java.util.Stack;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import java.util.stream.Collectors;

import javax.management.Query;

import com.google.common.base.Stopwatch;

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

	private static class SearchTreeNode {

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

	public CheckResult check(CFA cfa, final int k) {
		Stopwatch sw = Stopwatch.createUnstarted();
		sw.start();

		SearchTreeNode.count = 0;
		SolverManager manager = new Z3SolverManager();
		Solver solver = manager.createSolver(true, true);

		CfaLoc init = cfa.getInitLoc();
		CfaLoc error = cfa.getErrorLoc();

		VarIndexes.Builder viBuilder = VarIndexes.builder(0);
		VarIndexes vi = viBuilder.build();

			List<CfaLoc> avoid = new ArrayList<>();
			// Find all nodes which cannot reach error
			Stack<CfaLoc> errorReach = new Stack<>();
			List<CfaLoc> discovered = new ArrayList<>();
			errorReach.push(error);

			while (!errorReach.isEmpty()) {
				CfaLoc loc = errorReach.pop();
				if (!discovered.contains(loc)) {
					discovered.add(loc);
					for (CfaEdge edge : loc.getInEdges()) {
						errorReach.push(edge.getSource());
					}
				}
			}

		cfa.getLocs().stream().filter(l -> !discovered.contains(l)).forEach(l -> avoid.add(l));

		Queue<SearchTreeNode> queue = new ArrayDeque<>();
		queue.add(new SearchTreeNode(0, null, init, Collections.emptyList())); // add the initial node

		while (!queue.isEmpty()) {
			SearchTreeNode node = queue.poll();
			int depth = node.getDepth();

			if (node.getLoc() == error) {
				this.log.writeln("Found an error path with the length of " + node.getDepth(), 6);
				this.log.writeln("Stopwatch: " + sw.elapsed(TimeUnit.MILLISECONDS), 6);

				List<Stmt> stmts = this.getNodeStatements(node);

				StmtToExprResult exprs = StmtUnroller.transform(stmts, vi);
				//vi = exprs.getIndexes();

				solver.push();
				this.log.writeln("Exprs: " + exprs.getExprs(), 7, 1);
				solver.add(exprs.getExprs());

				solver.getAssertions().forEach(a -> this.log.writeln("Clause: " + a.toString(), 7, 1));

				this.log.writeln("Running solver...", 6);
				SolverStatus status = solver.check();
				if (status == SolverStatus.SAT) {
					this.log.writeln("Solver found a solution, check FAILED.", 1);
					this.log.writeln("System model: " + solver.getModel().toString(), 2);
					sw.stop();
					return CheckResult.CHECK_FAILED;
				}
				this.log.writeln("Solver finished, status: " + solver.getStatus(), 6);

				solver.pop();
			} else if (depth + 1 < k) {
				this.log.writeln("k=" + (depth + 1), 7);
				//this.log.writeln("k=" + (node.getDepth() + 1), 6, 1);
				for (CfaEdge edge : node.getLoc().getOutEdges()) {
					CfaLoc loc = edge.getTarget();
					if (!avoid.contains(loc)) {
						List<Stmt> stmts = edge.getStmts();
						int d2 = node.getDepth() + 1;

						SearchTreeNode stn = new SearchTreeNode(d2, node, loc, stmts);
						queue.add(stn);
					}
				}

				if (node.getLoc().getInEdges().size() == 0) {
					avoid.add(node.getLoc());
				}
			}
		}

		sw.stop();
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

}
