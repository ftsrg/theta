package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Collection;
import java.util.stream.Collectors;

public final class XstsLts <S extends ExprState> implements LTS<XstsState<S>, XstsAction> {

	private final NonDetStmt trans;
	private final NonDetStmt env;
	private final NonDetStmt init;

	private final XstsStmtOptimizer<S> stmtOptimizer;

	private XstsLts(final XSTS xsts, final XstsStmtOptimizer<S> stmtOptimizer) {
		trans = xsts.getTran();
		env = xsts.getEnv();
		init = xsts.getInit();

		this.stmtOptimizer = stmtOptimizer;
	}

	public static <S extends ExprState> LTS<XstsState<S>, XstsAction> create(final XSTS xsts, final XstsStmtOptimizer<S> stmtOptimizer) {
		return new XstsLts<>(xsts,stmtOptimizer);
	}

	@Override
	public Collection<XstsAction> getEnabledActionsFor(XstsState<S> state) {
		NonDetStmt enabledSet;
		if (!state.isInitialized()) enabledSet = init;
		else if (state.lastActionWasEnv()) enabledSet = trans;
		else enabledSet = env;

		return enabledSet.getStmts().stream()
				.map(stmt -> stmtOptimizer.optimizeStmt(state,stmt))
				.map(XstsAction::create)
				.collect(Collectors.toList());
	}
}
