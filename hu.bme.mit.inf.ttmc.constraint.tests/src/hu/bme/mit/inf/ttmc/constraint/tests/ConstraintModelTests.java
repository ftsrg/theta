package hu.bme.mit.inf.ttmc.constraint.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.model.ConstraintSpecification;
import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModel;
import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModelCreator;
import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModelLoader;
import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.core.ConstraintManagerImpl;

public class ConstraintModelTests {

	@Test
	public void testSimple() throws IOException {
		final File file = new File("instances/simple.constraint");
		final String filePath = file.getAbsolutePath();
		final ConstraintSpecification specification = ConstraintModelLoader.getInstance().load(filePath);
		final ConstraintManager manager = new ConstraintManagerImpl();
		final ConstraintModel model = ConstraintModelCreator.create(manager, specification);
		
		System.out.println(model.getConstDecls());
		System.out.println(model.getConstraints());
	}

}
