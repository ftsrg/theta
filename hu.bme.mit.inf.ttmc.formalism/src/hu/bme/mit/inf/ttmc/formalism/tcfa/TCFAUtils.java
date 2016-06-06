package hu.bme.mit.inf.ttmc.formalism.tcfa;

import static hu.bme.mit.inf.ttmc.formalism.utils.FormalismUtils.collectVars;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class TCFAUtils {

	private TCFAUtils() {
	}

	public boolean isValidDataStmt(final Stmt stmt) {
		if (stmt instanceof HavocStmt) {
			final HavocStmt<?> havocStmt = (HavocStmt<?>) stmt;
			return !isClock(havocStmt.getVarDecl());

		} else if (stmt instanceof AssignStmt) {
			final AssignStmt<?, ?> assignStmt = (AssignStmt<?, ?>) stmt;
			return !isClock(assignStmt.getVarDecl())
					&& collectVars(assignStmt.getExpr()).stream().allMatch(v -> !isClock(v));

		} else if (stmt instanceof AssumeStmt) {
			final AssumeStmt assumeStmt = (AssumeStmt) stmt;
			return collectVars(assumeStmt.getCond()).stream().allMatch(v -> !isClock(v));

		} else {
			return false;
		}
	}

	private static boolean isClock(final VarDecl<?> varDecl) {
		return varDecl instanceof ClockDecl;
	}

}
