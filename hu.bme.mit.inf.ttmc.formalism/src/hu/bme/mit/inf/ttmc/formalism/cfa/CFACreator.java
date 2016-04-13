package hu.bme.mit.inf.ttmc.formalism.cfa;

import hu.bme.mit.inf.ttmc.formalism.cfa.impl.LBECreator;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.SBECreator;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class CFACreator {

	public static CFA createSBE(final Stmt stmt) {
		return SBECreator.create(stmt);
	}

	public static CFA createLBE(final Stmt stmt) {
		return LBECreator.create(stmt);
	}

}
