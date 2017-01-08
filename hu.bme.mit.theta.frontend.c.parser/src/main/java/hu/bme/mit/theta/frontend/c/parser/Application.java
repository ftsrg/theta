package hu.bme.mit.theta.frontend.c.parser;


import java.util.stream.Collectors;

import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.frontend.c.Optimizer;
import hu.bme.mit.theta.frontend.c.dependency.CallGraph;
import hu.bme.mit.theta.frontend.c.dependency.utils.DependencyVisualizer;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.GlobalContext;
import hu.bme.mit.theta.frontend.c.ir.utils.FunctionVisualizer;
import hu.bme.mit.theta.frontend.c.transform.ConstantPropagator;
import hu.bme.mit.theta.frontend.c.transform.DeadBranchEliminator;
import hu.bme.mit.theta.frontend.c.transform.FunctionInliner;

public class Application {

	public static void main(String[] args) throws Exception {
		//final String file = "src/test/resources/all.c";
		final String file = "src/test/resources/s3_clnt_1_false.c";
		//Parser.dumpEclipseAst(file);
		
		GlobalContext context = Parser.parse(file);
		GraphvizWriter writer = new GraphvizWriter();
		
		System.out.println(writer.writeString(DependencyVisualizer.visualizeCallGraph(CallGraph.buildCallGraph(context))));

		Optimizer opt = new Optimizer(context);
		opt.setLogger(new ConsoleLogger(1000));
		
		//opt.addTransformation(new FunctionInliner());
		opt.addTransformation(new ConstantPropagator());
		opt.addTransformation(new DeadBranchEliminator());
		opt.transform();
		
		opt.dump();
		
				
	}
	
}
