package hu.bme.mit.inf.ttmc.cegar.tests.performance;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.cegar.common.CEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.InterpolatingCEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.InterpolatingCEGARBuilder.InterpolationMethod;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.Formatter;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.impl.ExcelFormatter;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.VisibleCEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.VisibleCEGARBuilder.VarCollectionMethod;

public class PerfTestHardware extends PerfTestBase {

	private static final int TIMEOUT = 5 * 60 * 1000;
	private static final Formatter FORMATTER = new ExcelFormatter();

	@SuppressWarnings("serial")
	@Test
	public void testHardware() {
		//final IModelLoader loader = new AIGERFileModelLoaderOptimized();
		final IModelLoader loader = new AIGERFileModelLoaderSimple();

		final List<TestCase> testCases = new ArrayList<TestCase>() {
			{
				add(new TestCase("models/hardware/ringp0.aag", false, loader));
				add(new TestCase("models/hardware/ringp0neg.aag", false, loader));
				add(new TestCase("models/hardware/shortp0.aag", false, loader));
				add(new TestCase("models/hardware/shortp0neg.aag", false, loader));
				add(new TestCase("models/hardware/srg5ptimo.aag", false, loader));
				add(new TestCase("models/hardware/srg5ptimoneg.aag", false, loader));
				add(new TestCase("models/hardware/srg5ptimonegnv.aag", false, loader));
				add(new TestCase("models/hardware/nusmv.syncarb5_2.B.aag", true, loader));
				add(new TestCase("models/hardware/nusmv.syncarb10_2.B.aag", true, loader));
				add(new TestCase("models/hardware/mutexp0.aag", false, loader));
				add(new TestCase("models/hardware/mutexp0neg.aag", false, loader));
				add(new TestCase("models/hardware/pdtpmsarbiter.aag", true, loader));

			}
		};
		final List<CEGARBuilder> configurations = new ArrayList<CEGARBuilder>() {
			{
				add(new VisibleCEGARBuilder().logger(null).visualizer(null).useCNFTransformation(false)
						.varCollectionMethod(VarCollectionMethod.CraigItp));
				add(new VisibleCEGARBuilder().logger(null).visualizer(null).useCNFTransformation(false)
						.varCollectionMethod(VarCollectionMethod.SequenceItp));
				add(new VisibleCEGARBuilder().logger(null).visualizer(null).useCNFTransformation(false)
						.varCollectionMethod(VarCollectionMethod.UnsatCore));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Craig).incrementalModelChecking(true)
						.useCNFTransformation(false));
				add(new InterpolatingCEGARBuilder().logger(null).visualizer(null).interpolationMethod(InterpolationMethod.Sequence)
						.incrementalModelChecking(true).useCNFTransformation(false));
			}
		};

		run(testCases, configurations, TIMEOUT, FORMATTER);
	}

}
