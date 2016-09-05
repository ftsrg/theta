package hu.bme.mit.inf.theta.formalism.cfa;

import hu.bme.mit.inf.theta.formalism.cfa.impl.LbeCreator;
import hu.bme.mit.inf.theta.formalism.cfa.impl.SbeCreator;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;

public class CfaCreator {

	public static CFA createSBE(final Stmt stmt) {
		return SbeCreator.create(stmt);
	}

	public static CFA createLBE(final Stmt stmt) {
		return LbeCreator.create(stmt);
	}

}
