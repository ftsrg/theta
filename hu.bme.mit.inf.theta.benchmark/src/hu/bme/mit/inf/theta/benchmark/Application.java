package hu.bme.mit.inf.theta.benchmark;

import java.io.IOException;
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
import hu.bme.mit.inf.theta.frontend.transform.FunctionInliner;
import hu.bme.mit.inf.theta.frontend.transform.LoopUnroller;

public class Application {

	public static void main(String[] args) throws IOException {
		System.in.read();
		int timeout = 36000000;

		BenchmarkConfiguration trivialOpt0 = new BenchmarkConfiguration("trivial_opt0", "benchmarks/trivial", timeout);
		trivialOpt0.setMaxBmcDepth(100);
		trivialOpt0.setSlice(false);
		//trivialOpt0.run();

		BenchmarkConfiguration trivialOpt1 = new BenchmarkConfiguration("trivial_opt1", "benchmarks/trivial", timeout);
		trivialOpt1.setMaxBmcDepth(100);
		trivialOpt1.addFunctionTransformer(new ConstantPropagator());
		trivialOpt1.addFunctionTransformer(new DeadBranchEliminator());
		trivialOpt1.setSlice(true);
		//trivialOpt1.run();

		BenchmarkConfiguration trivialOpt2 = new BenchmarkConfiguration("trivial_opt2", "benchmarks/trivial", timeout);
		trivialOpt2.setMaxBmcDepth(100);
		trivialOpt2.addFunctionTransformer(new ConstantPropagator());
		trivialOpt2.addFunctionTransformer(new DeadBranchEliminator());
		trivialOpt2.addFunctionTransformer(new LoopUnroller(10));
		trivialOpt2.addContextTransformer(new FunctionInliner());
		trivialOpt2.setSlice(true);
		//trivialOpt2.run();

		BenchmarkConfiguration locksOpt0 = new BenchmarkConfiguration("locks_opt0", "benchmarks/locks", timeout);
		locksOpt0.setMaxBmcDepth(100);
		locksOpt0.setSlice(false);
		//locksOpt0.run();

		BenchmarkConfiguration locksOpt1 = new BenchmarkConfiguration("locks_opt1", "benchmarks/locks", timeout);
		locksOpt1.setMaxBmcDepth(100);
		locksOpt1.setSlice(true);
		//locksOpt1.run();

		BenchmarkConfiguration locksOpt2 = new BenchmarkConfiguration("locks_opt2", "benchmarks/locks", timeout);
		locksOpt2.setMaxBmcDepth(100);
		locksOpt2.setSlice(true);
		locksOpt2.addFunctionTransformer(new ConstantPropagator());
		locksOpt2.addFunctionTransformer(new DeadBranchEliminator());
		//locksOpt2.run();

		BenchmarkConfiguration ecaOpt2 = new BenchmarkConfiguration("eca_opt2", "benchmarks/eca", timeout);
		ecaOpt2.addFunctionTransformer(new ConstantPropagator());
		ecaOpt2.addFunctionTransformer(new DeadBranchEliminator());
		ecaOpt2.addContextTransformer(new FunctionInliner());
		ecaOpt2.addPostContextFunctionTransformer(new ConstantPropagator());
		ecaOpt2.addPostContextFunctionTransformer(new DeadBranchEliminator());
		ecaOpt2.setMaxBmcDepth(1000);
		ecaOpt2.setLogLevel(7);
		ecaOpt2.setSlice(true);
		ecaOpt2.run();

		BenchmarkConfiguration trivial2Opt2 = new BenchmarkConfiguration("triv2", "benchmarks/trivial2", timeout);
		trivial2Opt2.setMaxBmcDepth(30);
		trivial2Opt2.addFunctionTransformer(new ConstantPropagator());
		trivial2Opt2.addFunctionTransformer(new DeadBranchEliminator());
		trivial2Opt2.addContextTransformer(new FunctionInliner());
		trivial2Opt2.setSlice(true);
		trivial2Opt2.setLogLevel(7);
		trivial2Opt2.run();

		// FIXME: I don't know why is this needed, but otherwise a thread would do an infinite loop
		System.exit(0);
	}


}
