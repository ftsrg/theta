package hu.bme.mit.theta.formalism.cfa.creator;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.cfa.CFA;

public class CfaCreator {

	public static CFA createSBE(final Stmt stmt) {
		return SbeCreator.create(stmt);
	}

	public static CFA createLBE(final Stmt stmt) {
		return LbeCreator.create(stmt);
	}

}
