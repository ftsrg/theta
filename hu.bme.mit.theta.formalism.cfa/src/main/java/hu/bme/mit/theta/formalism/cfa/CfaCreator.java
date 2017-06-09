package hu.bme.mit.theta.formalism.cfa;

import hu.bme.mit.theta.core.stmt.Stmt;

public class CfaCreator {

	public static CFA createSBE(final Stmt stmt) {
		return SbeCreator.create(stmt);
	}

	public static CFA createLBE(final Stmt stmt) {
		return LbeCreator.create(stmt);
	}

}
