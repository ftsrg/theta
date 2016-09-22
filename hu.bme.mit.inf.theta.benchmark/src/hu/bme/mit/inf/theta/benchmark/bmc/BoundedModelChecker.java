package hu.bme.mit.inf.theta.benchmark.bmc;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Stack;
import java.util.function.Function;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.benchmark.bmc.StmtToExprTransformer.StmtToExprResult;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.inf.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.theta.solver.Solver;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.SolverStatus;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

public class BoundedModelChecker {

	public enum CheckResult {
		CHECK_FAILED, CHECK_PASSED, CHECK_UNKNOWN
	}

	private Logger log;

	public BoundedModelChecker(Logger log) {
		this.log = log;
	}

	public CheckResult checkAll(Collection<CFA> cfas, int k) {
		for (CFA cfa : cfas) {
			if (this.check(cfa, k) == CheckResult.CHECK_FAILED)
				return CheckResult.CHECK_FAILED;
		}

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

		StmtToExprTransformer stmtToExpr = new StmtToExprTransformer(VarMap.create());

		for (int i = 0; i < k; i++) {
			List<List<CfaEdge>> paths = new ArrayList<>();

			this.search(cfa.getInitLoc(), cfa.getErrorLoc(), i, new Stack<>(), paths);

			if (!paths.isEmpty()) { // there is an error path
				for (List<CfaEdge> path : paths) {
					solver.push();
					this.log.writeln("Found an error path with length of " + i, 6);

					IndexMap im = IndexMap.create();
					for (CfaEdge edge : path) {
						for (Stmt stmt : edge.getStmts()) {
							StmtToExprResult result = stmtToExpr.transform(stmt, im);
							im = result.indexMap;

							result.exprs.forEach(expr -> {
								this.log.writeln("Clause: " + expr.toString(), 7, 0);
								solver.add(expr);
							});
						}
					}

					SolverStatus status = solver.check();
					if (status == SolverStatus.SAT) {
						this.log.writeln("Check FAILED, system model:", 0);
						this.log.writeln(solver.getModel().toString(), 0, 1);

						return CheckResult.CHECK_FAILED;
					} else if (status == SolverStatus.UNKNOWN) {
						this.log.writeln("Check UNKNOWN, system assertions:", 5);
						this.log.writeln(solver.getAssertions().toString(), 5);
					}
					solver.pop();
				}
			}
		}

		return CheckResult.CHECK_PASSED;
	}

	private boolean search(CfaLoc node, CfaLoc target, int depth, Stack<CfaEdge> path, List<List<CfaEdge>> paths) {
		if (depth == 0 && node == target)
			return true;

		if (depth > 0) {
			for (CfaEdge out : node.getOutEdges()) {
				path.push(out);
				if (true == search(out.getTarget(), target, depth - 1, path, paths)) { // Found it
					paths.add(new ArrayList<>(path));
				}

				path.pop();
			}
		}

		return false;
	}


}
