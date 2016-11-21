package hu.bme.mit.theta.analysis.tcfa.zone;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaExpr;
import hu.bme.mit.theta.analysis.tcfa.TcfaExpr.ClockExpr;
import hu.bme.mit.theta.analysis.tcfa.TcfaStmt;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.op.ClockOp;

final class TcfaZoneTransferFunction implements TransferFunction<ZoneState, TcfaAction, ZonePrecision> {

	private final static TcfaZoneTransferFunction INSTANCE = new TcfaZoneTransferFunction();

	private TcfaZoneTransferFunction() {
	}

	static TcfaZoneTransferFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getSuccStates(final ZoneState state, final TcfaAction action,
			final ZonePrecision precision) {

		final ZoneState succState = post(state, action, precision);

		if (succState.isBottom()) {
			return ImmutableSet.of();
		} else {
			return ImmutableSet.of(succState);
		}
	}

	ZoneState post(final ZoneState state, final TcfaAction action, final ZonePrecision precision) {
		final ZoneState.ZoneOperations succStateBuilder = state.project(precision.getClocks());

		for (final TcfaExpr invar : action.getSourceInvars()) {
			if (invar.isClockExpr()) {
				final ClockExpr clockExpr = invar.asClockExpr();
				final ClockConstr constr = clockExpr.getClockConstr();
				succStateBuilder.and(constr);
			}
		}

		if (!action.getEdge().getSource().isUrgent()) {
			succStateBuilder.up();

			for (final TcfaExpr invar : action.getSourceInvars()) {
				if (invar.isClockExpr()) {
					final ClockExpr clockExpr = invar.asClockExpr();
					final ClockConstr constr = clockExpr.getClockConstr();
					succStateBuilder.and(constr);
				}
			}
		}

		for (final TcfaStmt tcfaStmt : action.getTcfaStmts()) {
			if (tcfaStmt.isClockStmt()) {
				final ClockOp op = tcfaStmt.asClockStmt().getClockOp();
				succStateBuilder.execute(op);
			}
		}

		for (final TcfaExpr invar : action.getTargetInvars()) {
			if (invar.isClockExpr()) {
				final ClockExpr clockExpr = invar.asClockExpr();
				final ClockConstr constr = clockExpr.getClockConstr();
				succStateBuilder.and(constr);
			}
		}

		return succStateBuilder.done();
	}

}
