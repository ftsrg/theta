package hu.bme.mit.inf.theta.benchmark;

import java.util.List;

import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker;
import hu.bme.mit.inf.theta.benchmark.bmc.BoundedModelChecker.CheckResult;
import hu.bme.mit.inf.theta.code.Parser;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.transform.ConstantPropagator;
import hu.bme.mit.inf.theta.frontend.transform.DeadBranchEliminator;
import hu.bme.mit.inf.theta.frontend.transform.LoopUnroller;

public class Application {

	public static void main(String[] args) {
		BenchmarkConfiguration trivialOpt0 = new BenchmarkConfiguration("trivial_opt0", "benchmarks/trivial", 5000);
		trivialOpt0.setMaxBmcDepth(100);
		trivialOpt0.setSlice(false);
		//trivialOpt0.run();

		BenchmarkConfiguration trivialOpt1 = new BenchmarkConfiguration("trivial_opt1", "benchmarks/trivial", 5000);
		trivialOpt1.setMaxBmcDepth(100);
		trivialOpt1.addFunctionTransformer(new ConstantPropagator());
		trivialOpt1.addFunctionTransformer(new DeadBranchEliminator());
		trivialOpt1.setSlice(true);
		//trivialOpt1.run();

		BenchmarkConfiguration trivialOpt2 = new BenchmarkConfiguration("trivial_opt2", "benchmarks/trivial", 5000);
		trivialOpt2.setMaxBmcDepth(100);
		trivialOpt2.addFunctionTransformer(new ConstantPropagator());
		trivialOpt2.addFunctionTransformer(new DeadBranchEliminator());
		trivialOpt2.addFunctionTransformer(new LoopUnroller(10));
		trivialOpt2.setSlice(true);
		//trivialOpt2.run();

		BenchmarkConfiguration locksOpt0 = new BenchmarkConfiguration("locks_opt0", "benchmarks/eca", 5000);
		locksOpt0.setMaxBmcDepth(100);
		locksOpt0.setSlice(true);
		locksOpt0.run();

		// FIXME: ???
		System.exit(0);
	}

	public static CheckResult runBenchmark(String file, Logger log) {
		GlobalContext context = Parser.parse(file);
		Optimizer opt = new Optimizer(context);
		opt.setLogger(log);

		//opt.addFunctionTransformer(new LoopUnroller(10));
		opt.addFunctionTransformer(new ConstantPropagator());
		opt.addFunctionTransformer(new DeadBranchEliminator());

		//opt.addContextTransformer(new FunctionInliner());

		opt.transform();

		opt.dump();

		List<CFA> cfas = opt.createCfaSlices();
		cfas.forEach(cfa -> {
			log.writeHeader("CFA SLICES", 1);
			log.writeln(CfaPrinter.toGraphvizSting(cfa), 1);
		});

		BoundedModelChecker bmc = new BoundedModelChecker(log);
		CheckResult res = bmc.checkAll(opt.createCfaSlices(), 30);

		return res;
	}


}
