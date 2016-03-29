package hu.bme.mit.inf.ttmc.formalism.cfa;

import hu.bme.mit.inf.ttmc.formalism.cfa.impl.LBECreator;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.SBECreator;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;

public class CFACreator {

	public static CFA createSBE(final ProgramManager manager, final Stmt stmt) {
		return SBECreator.create(manager, stmt);
	}

	public static CFA createLBE(final ProgramManager manager, final Stmt stmt) {
		return LBECreator.create(manager, stmt);
	}

}
