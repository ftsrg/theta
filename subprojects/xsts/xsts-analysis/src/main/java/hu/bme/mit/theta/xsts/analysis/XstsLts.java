package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.StmtUnroller;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Collection;
import java.util.stream.Collectors;

public final class XstsLts implements LTS<XstsState, XstsAction> {

	private final NonDetStmt trans;
	private final NonDetStmt env;
	private final NonDetStmt init;

	private final XstsStmtUnroller stmtUnroller;

	private XstsLts(final XSTS xsts, final XstsStmtUnroller stmtUnroller) {
		trans = xsts.getTran();
		env = xsts.getEnv();
		init = xsts.getInit();

		this.stmtUnroller = stmtUnroller;
	}

	public static LTS<XstsState, XstsAction> create(final XSTS xsts, final XstsStmtUnroller stmtUnroller) {
		return new XstsLts(xsts,stmtUnroller);
	}

	@Override
	public Collection<XstsAction> getEnabledActionsFor(XstsState state) {
		NonDetStmt enabledSet;
		if (!state.isInitialized()) enabledSet = init;
		else if (state.lastActionWasEnv()) enabledSet = trans;
		else enabledSet = env;

		return enabledSet.getStmts().stream()
				.map(stmt -> stmtUnroller.unrollStmt(state,stmt))
				.map(XstsAction::create)
				.collect(Collectors.toList());
	}
}
