package hu.bme.mit.inf.ttmc.system.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.impl.STSCNFTransformation;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.impl.STSITETransformation;
import hu.bme.mit.inf.ttmc.system.model.SystemSpecification;
import hu.bme.mit.inf.ttmc.system.ui.SystemModel;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelCreator;
import hu.bme.mit.inf.ttmc.system.ui.SystemModelLoader;

public class SystemModelTests {

	@Test
	public void testSimple() throws IOException {
		final File file = new File("instances/simple1.system");
		final String filePath = file.getAbsolutePath();
		final SystemSpecification specification = SystemModelLoader.getInstance().load(filePath);
		final STSManager manager = new STSManagerImpl(new ConstraintManagerImpl());
		final SystemModel model = SystemModelCreator.create(manager, specification);

		for (STS sts : model.getSTSs()) {
			sts = new STSCNFTransformation(manager).transform(
					new STSITETransformation(manager).transform(sts));
			System.out.println(sts.getVars());
			System.out.println(sts.getInit());
			System.out.println(sts.getInvar());
			System.out.println(sts.getTrans());
			System.out.println(sts.getProp());
		}
	}
}
