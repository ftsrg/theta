package hu.bme.mit.inf.ttmc.formalism.program;

import hu.bme.mit.inf.ttmc.formalism.FormalismManager;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;

public interface ProgramManager extends FormalismManager {

	@Override
	public VarDeclFactory getDeclFactory();

}
