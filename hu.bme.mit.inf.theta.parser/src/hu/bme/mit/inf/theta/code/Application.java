package hu.bme.mit.inf.theta.code;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import org.eclipse.core.runtime.CoreException;

import hu.bme.mit.inf.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.cfa.FunctionToCFATransformer;
import hu.bme.mit.inf.theta.frontend.dependency.CallGraph;
import hu.bme.mit.inf.theta.frontend.dependency.ProgramDependency;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.frontend.ir.utils.IrPrinter;
import hu.bme.mit.inf.theta.frontend.transform.ConstantPropagator;
import hu.bme.mit.inf.theta.frontend.transform.DeadBranchEliminator;
import hu.bme.mit.inf.theta.frontend.transform.FunctionInliner;
import hu.bme.mit.inf.theta.frontend.transform.FunctionSlicer;

class Application {

	public static void main(String[] args)
			throws CoreException, FileNotFoundException, IOException, InterruptedException {

		GlobalContext context = Parser.parse("func-cg.c");
		Optimizer opt = new Optimizer(context);
		opt.setLogger(new ConsoleLogger(7));

		CallGraph cg = CallGraph.buildCallGraph(context);

		//opt.addFunctionTransformer(new ConstantPropagator());
		//opt.addFunctionTransformer(new DeadBranchEliminator());
		//opt.addContextTransformer(new FunctionInliner());
		//opt.dump();

		opt.transform();

		System.out.println(IrPrinter.callGraph(cg));
		//opt.dump();

		//System.out.println(IrPrinter.toGraphvizString(context.getFunctionByName("main")));

		//List<CFA> cfas = opt.createCfaSlices();
	}
}
