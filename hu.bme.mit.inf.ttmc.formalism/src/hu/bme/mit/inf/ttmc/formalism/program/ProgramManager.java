package hu.bme.mit.inf.ttmc.formalism.program;

import hu.bme.mit.inf.ttmc.formalism.FormalismManager;
import hu.bme.mit.inf.ttmc.formalism.common.factory.StmtFactory;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramExprFactory;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramTypeFactory;

public interface ProgramManager extends FormalismManager {

	@Override
	public ProgramTypeFactory getTypeFactory();

	@Override
	public ProgramDeclFactory getDeclFactory();

	@Override
	public ProgramExprFactory getExprFactory();

	public StmtFactory getStmtFactory();

}
