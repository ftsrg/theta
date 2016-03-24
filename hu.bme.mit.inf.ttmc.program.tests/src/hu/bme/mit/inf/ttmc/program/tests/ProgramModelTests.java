package hu.bme.mit.inf.ttmc.program.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.formalism.program.impl.ProgramManagerImpl;
import hu.bme.mit.inf.ttmc.program.model.ProgramSpecification;
import hu.bme.mit.inf.ttmc.program.ui.ProgramModel;
import hu.bme.mit.inf.ttmc.program.ui.ProgramModelCreator;
import hu.bme.mit.inf.ttmc.program.ui.ProgramModelLoader;

public class ProgramModelTests {

	@Test
	public void testLinear() throws IOException {
		final File file = new File("instances/linear.program");
		final String filePath = file.getAbsolutePath();
		final ProgramSpecification specification = ProgramModelLoader.getInstance().load(filePath);
		final ProgramManager manager = new ProgramManagerImpl(new ConstraintManagerImpl());
		final ProgramModel model = ProgramModelCreator.create(manager, specification);
		final ProcDecl<? extends Type> procDecl = model.getProcDecls().iterator().next();
		System.out.println(procDecl.getStmt().get());
	}

}
