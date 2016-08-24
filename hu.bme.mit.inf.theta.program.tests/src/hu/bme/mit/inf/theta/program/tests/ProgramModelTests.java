package hu.bme.mit.inf.theta.program.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.program.model.ProgramSpecification;
import hu.bme.mit.inf.theta.program.ui.ProgramModel;
import hu.bme.mit.inf.theta.program.ui.ProgramModelCreator;
import hu.bme.mit.inf.theta.program.ui.ProgramModelLoader;

public class ProgramModelTests {

	@Test
	public void test() throws IOException {
		final File file = new File("instances/linear.program");
		final String filePath = file.getAbsolutePath();
		final ProgramSpecification specification = ProgramModelLoader.getInstance().load(filePath);
		final ProgramModel model = ProgramModelCreator.create(specification);
		final ProcDecl<? extends Type> procDecl = model.getProcDecls().iterator().next();
		System.out.println(procDecl);
	}

}
