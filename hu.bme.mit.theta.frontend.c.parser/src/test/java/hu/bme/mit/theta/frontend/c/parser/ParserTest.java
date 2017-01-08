package hu.bme.mit.theta.frontend.c.parser;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.junit.Test;

import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.utils.CfaVisualizer;
import hu.bme.mit.theta.frontend.c.Optimizer;
import hu.bme.mit.theta.frontend.c.cfa.SbeToLbeTransformer;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph;
import hu.bme.mit.theta.frontend.c.ir.GlobalContext;
import hu.bme.mit.theta.frontend.c.transform.ConstantPropagator;
import hu.bme.mit.theta.frontend.c.transform.DeadBranchEliminator;
import hu.bme.mit.theta.frontend.c.transform.FunctionInliner;

public class ParserTest {

	@Test
	public void test() throws CoreException, FileNotFoundException, IOException, InterruptedException {

		GlobalContext context = Parser.parse("src/test/resources/simple.c");
		Optimizer opt = new Optimizer(context);
		opt.setLogger(new ConsoleLogger(7));

		CallGraph cg = CallGraph.buildCallGraph(context);

		// opt.addPostContextFunctionTransformer(new ConstantPropagator());
		// opt.addPostContextFunctionTransformer(new DeadBranchEliminator());
		// opt.dump();

		opt.inlineGlobalVariables();
		opt.transform();

		opt.dump();

		// System.out.println(IrPrinter.toGraphvizString(context.getFunctionByName("main")));

		List<CFA> cfas = opt.getProgramSlices();
		cfas.forEach(cfa -> {
			System.out.println(new GraphvizWriter().writeString(CfaVisualizer.visualize(cfa)));
			System.out.println(
					new GraphvizWriter().writeString(CfaVisualizer.visualize(SbeToLbeTransformer.transform(cfa))));
		});
	}
}
