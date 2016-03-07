package hu.bme.mit.inf.ttmc.system.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.factory.ProgramFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
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
		final ConstraintManager manager = new ConstraintManagerImpl();
		final SystemModelCreator creator = new SystemModelCreator(manager, new ProgramFactoryImpl(), specification);
		final SystemModel model = creator.createSystemModel();

		for (STS sts : model.getSTSs()) {
			System.out.println(sts.getVars());
			System.out.println(sts.getInit());
			System.out.println(sts.getInvar());
			System.out.println(sts.getTrans());
		}
	}
}
