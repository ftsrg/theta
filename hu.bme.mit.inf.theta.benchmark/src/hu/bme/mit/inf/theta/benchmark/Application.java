package hu.bme.mit.inf.theta.benchmark;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.theta.benchmark.BenchmarkConfiguration.MeasureResult;
import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker;
import hu.bme.mit.inf.theta.benchmark.bmc.ErrorSearch;
import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker.CheckResult;
import hu.bme.mit.inf.theta.code.Parser;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.transform.ConstantPropagator;
import hu.bme.mit.inf.theta.frontend.transform.DeadBranchEliminator;
import hu.bme.mit.inf.theta.frontend.transform.FunctionInliner;
import hu.bme.mit.inf.theta.frontend.transform.LoopUnroller;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

public class Application {


	public static void main(String args[]) {
		GlobalContext context = Parser.parse("benchmarks/locks/locks14_false.c");

		Optimizer opt = new Optimizer(context);
		opt.getProgramSlices().forEach(slice -> {
			SolverManager sm = new Z3SolverManager();
			Logger log = new ConsoleLogger(2);

			log.writeHeader("Slice size: " + slice.getLocs().size(), 0);

			ErrorSearch bmc = new ErrorSearch(slice, sm.createSolver(true, true), log);
			bmc.check(200);
		});

	}


}
