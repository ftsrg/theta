package hu.bme.mit.theta.splittingcegar.ui.performance;

import java.util.ArrayList;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import hu.bme.mit.theta.splittingcegar.clustered.ClusteredCEGARBuilder;
import hu.bme.mit.theta.splittingcegar.common.CEGARBuilder;
import hu.bme.mit.theta.splittingcegar.interpolating.InterpolatingCEGARBuilder;
import hu.bme.mit.theta.splittingcegar.interpolating.InterpolatingCEGARBuilder.InterpolationMethod;
import hu.bme.mit.theta.splittingcegar.ui.formatters.Formatter;
import hu.bme.mit.theta.splittingcegar.ui.formatters.impl.ExcelFormatter;
import hu.bme.mit.theta.splittingcegar.visible.VisibleCEGARBuilder;
import hu.bme.mit.theta.splittingcegar.visible.VisibleCEGARBuilder.VarCollectionMethod;

public class PerfTestSimple extends PerfTestBase {

	private static final int TIMEOUT = 10 * 1000;
	private static final Formatter FORMATTER = new ExcelFormatter();

	@SuppressWarnings("serial")
	@Test
	@Ignore
	public void testSimple() {
		final IModelLoader loader = new SystemFileModelLoader();

		final List<TestCase> testCases = new ArrayList<TestCase>() {
			{
				add(new TestCase("src/test/resources/models/simple/simple1.system", false, loader));
				add(new TestCase("src/test/resources/models/simple/simple2.system", true, loader));
				add(new TestCase("src/test/resources/models/simple/simple3.system", false, loader));
				add(new TestCase("src/test/resources/models/simple/counter.system", true, loader));
				add(new TestCase("src/test/resources/models/simple/counter_bad.system", false, loader));
				add(new TestCase("src/test/resources/models/simple/counter_parametric.system", true, loader));
				add(new TestCase("src/test/resources/models/simple/boolean1.system", false, loader));
				add(new TestCase("src/test/resources/models/simple/boolean2.system", false, loader));
				add(new TestCase("src/test/resources/models/simple/readerswriters.system", true, loader));
				add(new TestCase("src/test/resources/models/simple/loop.system", true, loader));
				add(new TestCase("src/test/resources/models/simple/loop_bad.system", false, loader));
			}
		};
		final List<CEGARBuilder> configurations = new ArrayList<CEGARBuilder>() {
			{
				add(new ClusteredCEGARBuilder().logger(null).visualizer(null));
				add(new VisibleCEGARBuilder().logger(null).visualizer(null).useCNFTransformation(false)
						.varCollectionMethod(VarCollectionMethod.CraigItp));
				add(new VisibleCEGARBuilder().logger(null).visualizer(null).useCNFTransformation(false)
						.varCollectionMethod(VarCollectionMethod.SequenceItp));
				add(new VisibleCEGARBuilder().logger(null).visualizer(null).useCNFTransformation(false)
						.varCollectionMethod(VarCollectionMethod.UnsatCore));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null)
						.interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(false)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null)
						.interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null)
						.interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(true));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null)
						.interpolationMethod(InterpolationMethod.Sequence).incrementalModelChecking(true)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null)
						.interpolationMethod(InterpolationMethod.Sequence).incrementalModelChecking(true)
						.useCNFTransformation(true));
			}
		};

		run(testCases, configurations, TIMEOUT, FORMATTER);
	}

}
