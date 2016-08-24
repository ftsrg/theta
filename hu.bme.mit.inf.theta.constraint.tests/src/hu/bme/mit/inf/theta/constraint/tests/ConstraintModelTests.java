package hu.bme.mit.inf.theta.constraint.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.theta.constraint.model.ConstraintSpecification;
import hu.bme.mit.inf.theta.constraint.ui.ConstraintModel;
import hu.bme.mit.inf.theta.constraint.ui.ConstraintModelCreator;
import hu.bme.mit.inf.theta.constraint.ui.ConstraintModelLoader;

public class ConstraintModelTests {

	@Test
	public void testSimple() throws IOException {
		final File file = new File("instances/simple.constraint");
		final String filePath = file.getAbsolutePath();
		final ConstraintSpecification specification = ConstraintModelLoader.getInstance().load(filePath);
		final ConstraintModel model = ConstraintModelCreator.create(specification);

		System.out.println(model.getConstDecls());
		System.out.println(model.getConstraints());
	}

}
