package hu.bme.mit.inf.theta.system.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.system.model.SystemSpecification;
import hu.bme.mit.inf.theta.system.ui.SystemModel;
import hu.bme.mit.inf.theta.system.ui.SystemModelCreator;
import hu.bme.mit.inf.theta.system.ui.SystemModelLoader;

public class SystemModelTests {

	@Test
	public void testSimple() throws IOException {
		final File file = new File("instances/simple1.system");
		final String filePath = file.getAbsolutePath();
		final SystemSpecification specification = SystemModelLoader.getInstance().load(filePath);
		final SystemModel model = SystemModelCreator.create(specification);

		for (final STS sts : model.getSTSs()) {
			// sts = new STSCNFTransformation().transform(new
			// STSITETransformation().transform(sts));
			System.out.println(sts);
		}
	}
}
