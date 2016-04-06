package hu.bme.mit.inf.ttmc.program.tests;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFACreator;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.formalism.program.impl.ProgramManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CFAPrinter;
import hu.bme.mit.inf.ttmc.program.model.ProgramSpecification;
import hu.bme.mit.inf.ttmc.program.ui.ProgramModel;
import hu.bme.mit.inf.ttmc.program.ui.ProgramModelCreator;
import hu.bme.mit.inf.ttmc.program.ui.ProgramModelLoader;

public class ProgramModelTests {

	@Test
	public void testSBELinear() throws IOException {
		final File file = new File("instances/linear.program");
		final String filePath = file.getAbsolutePath();
		final ProgramSpecification specification = ProgramModelLoader.getInstance().load(filePath);
		final ProgramManager manager = new ProgramManagerImpl(new ConstraintManagerImpl());
		final ProgramModel model = ProgramModelCreator.create(manager, specification);
		final ProcDecl<? extends Type> procDecl = model.getProcDecls().iterator().next();
		final Stmt stmt = procDecl.getStmt().get();

		final CFA cfa = CFACreator.createSBE(manager, stmt);
		System.out.println(CFAPrinter.toGraphvizSting(cfa));
	}

	@Test
	public void testLBELinear() throws IOException {
		final File file = new File("instances/linear.program");
		final String filePath = file.getAbsolutePath();
		final ProgramSpecification specification = ProgramModelLoader.getInstance().load(filePath);
		final ProgramManager manager = new ProgramManagerImpl(new ConstraintManagerImpl());
		final ProgramModel model = ProgramModelCreator.create(manager, specification);
		final ProcDecl<? extends Type> procDecl = model.getProcDecls().iterator().next();
		final Stmt stmt = procDecl.getStmt().get();

		final CFA cfa = CFACreator.createLBE(manager, stmt);
		System.out.println(CFAPrinter.toGraphvizSting(cfa));
	}

}
