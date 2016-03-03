package hu.bme.mit.inf.ttmc.constraint.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.model.ConstraintSpecification;
import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModel;
import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModelCreator;
import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModelLoader;

public class ConstraintModelTests {

	@Test
	public void testSimple() throws IOException {
		final File file = new File("instances/simple.constraint");
		final String filePath = file.getAbsolutePath();
		final ConstraintSpecification specification = ConstraintModelLoader.getInstance().load(filePath);
		final ConstraintManager manager = new ConstraintManagerImpl();
		final ConstraintModelCreator creator = new ConstraintModelCreator(manager, specification);
		final ConstraintModel model = creator.create();
		
		System.out.println(model.getConstDecls());
	}

}
