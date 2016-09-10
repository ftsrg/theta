package hu.bme.mit.theta.splittingcegar.ui;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.theta.aiger.impl.AIGERLoaderSimple;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.impl.StsSpec;
import hu.bme.mit.theta.splittingcegar.common.CEGARLoop;
import hu.bme.mit.theta.splittingcegar.common.CEGARResult;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractState;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.GraphVizVisualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.interpolating.InterpolatingCEGARBuilder;
import hu.bme.mit.theta.splittingcegar.interpolating.InterpolatingCEGARBuilder.InterpolationMethod;

public class SandBox {

	private static final String MODELSPATH = "src/test/resources/models/";

	@Test
	public void test() throws IOException {

		// System.in.read();

		final String subPath = "simple/";
		final String modelName = "simple3.system";

		final Logger logger = new ConsoleLogger(10);
		final Visualizer visualizer = null; // new
											// GraphVizVisualizer("models/_output",
											// modelName, 100);
		final Visualizer debugVisualizer = new GraphVizVisualizer("src/test/resources/models/debug", modelName, 100,
				true);

		STS problem = null;

		if (modelName.endsWith(".system")) {
			final StsSpec stsSpec = StsDslManager.parse(MODELSPATH + subPath + modelName);
			problem = stsSpec.getAllSts().iterator().next();
		} else if (modelName.endsWith(".aag")) {
			problem = new AIGERLoaderSimple().load(MODELSPATH + subPath + modelName);
		}

		CEGARLoop cegar = null;

		// cegar = new
		// ClusteredCEGARBuilder().logger(logger).visualizer(visualizer).debug(debugVisualizer).build();
		// cegar = new
		// VisibleCEGARBuilder().logger(logger).visualizer(visualizer).useCNFTransformation(false)
		// .variableCollectionMethod(VariableCollectionMethod.UnsatCore).debug(debugVisualizer).build();

		cegar = new InterpolatingCEGARBuilder().logger(logger).visualizer(visualizer).useCNFTransformation(false)
				.collectFromSpecification(false).collectFromConditions(false).incrementalModelChecking(true)
				.interpolationMethod(InterpolationMethod.Craig)
				// .explicitVariable("lock_b0").explicitVariable("lock_b1")
				// .explicitVariable("loc")
				.debug(debugVisualizer).build();

		final CEGARResult result = cegar.check(problem);

		if (result.propertyHolds()) {
			final List<Expr<? extends BoolType>> ops = new ArrayList<>();
			for (final AbstractState as : result.getExploredStates()) {
				ops.add(as.createExpression());
			}

			// System.out.println(InvariantChecker.check(result.getSTS(),
			// Exprs.Or(ops)));

		}
	}
}
