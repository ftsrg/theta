package hu.bme.mit.inf.theta.code;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.CoreException;

import hu.bme.mit.inf.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;
import hu.bme.mit.inf.theta.frontend.Optimizer;
import hu.bme.mit.inf.theta.frontend.cfa.FunctionToCFATransformer;
import hu.bme.mit.inf.theta.frontend.cfa.SbeToLbeTransformer;
import hu.bme.mit.inf.theta.frontend.dependency.CallGraph;
import hu.bme.mit.inf.theta.frontend.dependency.ProgramDependency;
import hu.bme.mit.inf.theta.frontend.dependency.ProgramDependency.PDGNode;
import hu.bme.mit.inf.theta.frontend.dependency.CallGraph.CallGraphNode;
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

		GlobalContext context = Parser.parse("simple.c");
		Optimizer opt = new Optimizer(context);
		opt.setLogger(new ConsoleLogger(7));

		CallGraph cg = CallGraph.buildCallGraph(context);

		opt.addFunctionTransformer(new ConstantPropagator());
		opt.addFunctionTransformer(new DeadBranchEliminator());
		opt.addContextTransformer(new FunctionInliner());
		//opt.addPostContextFunctionTransformer(new ConstantPropagator());
		//opt.addPostContextFunctionTransformer(new DeadBranchEliminator());
		//opt.dump();

		opt.inlineGlobalVariables();
		opt.transform();

		opt.dump();


		//System.out.println(IrPrinter.toGraphvizString(context.getFunctionByName("main")));

		List<CFA> cfas = opt.getProgramSlices();
		cfas.forEach(cfa -> {
			System.out.println(CfaPrinter.toGraphvizSting(cfa));
			System.out.println(CfaPrinter.toGraphvizSting(SbeToLbeTransformer.transform(cfa)));
		});
	}
}
