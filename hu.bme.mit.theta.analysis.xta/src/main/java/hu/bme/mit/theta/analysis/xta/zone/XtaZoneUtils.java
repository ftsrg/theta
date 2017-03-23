package hu.bme.mit.theta.analysis.xta.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SyncedXtaAction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.ta.utils.impl.TaExpr;
import hu.bme.mit.theta.formalism.ta.utils.impl.TaStmt;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc.Kind;

public final class XtaZoneUtils {

	private XtaZoneUtils() {
	}

	public static ZoneState post(final ZoneState state, final XtaAction action, final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		if (action.isSimple()) {
			return postForSimpleAction(state, action.asSimple(), prec);
		} else if (action.isSynced()) {
			return postForSyncedAction(state, action.asSynced(), prec);
		} else {
			throw new AssertionError();
		}

	}

	private static ZoneState postForSimpleAction(final ZoneState state, final SimpleXtaAction action,
			final ZonePrec prec) {
		final ZoneState.Builder succStateBuilder = state.project(prec.getClocks());

		final Edge edge = action.getEdge();

		for (final Loc source : action.getSourceLocs()) {
			for (final Expr<BoolType> invar : source.getInvars()) {
				final TaExpr expr = TaExpr.of(invar);
				if (expr.isClockExpr()) {
					succStateBuilder.and(expr.asClockExpr().getClockConstr());
				}
			}
		}

		for (final Expr<BoolType> guard : edge.getGuards()) {
			final TaExpr expr = TaExpr.of(guard);
			if (expr.isClockExpr()) {
				succStateBuilder.and(expr.asClockExpr().getClockConstr());
			}
		}

		for (final AssignStmt<?, ?> update : edge.getUpdates()) {
			final TaStmt stmt = TaStmt.of(update);
			if (stmt.isClockStmt()) {
				succStateBuilder.execute(stmt.asClockStmt().getClockOp());
			}
		}

		for (final Loc target : action.getTargetLocs()) {
			for (final Expr<BoolType> invar : target.getInvars()) {
				final TaExpr expr = TaExpr.of(invar);
				if (expr.isClockExpr()) {
					succStateBuilder.and(expr.asClockExpr().getClockConstr());
				}
			}
		}

		if (shouldApplyDelay(action.getTargetLocs())) {
			succStateBuilder.up();
		}

		final ZoneState succState = succStateBuilder.build();
		return succState;
	}

	private static boolean shouldApplyDelay(final List<Loc> locs) {
		return locs.stream().allMatch(l -> l.getKind() == Kind.NORMAL);
	}

	private static ZoneState postForSyncedAction(final ZoneState state, final SyncedXtaAction asSynced,
			final ZonePrec prec) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	public static ZoneState pre(final ZoneState state, final SimpleXtaAction action, final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		if (action.isSimple()) {
			return preForSimpleAction(state, action.asSimple(), prec);
		} else if (action.isSynced()) {
			return preForSyncedAction(state, action.asSynced(), prec);
		} else {
			throw new AssertionError();
		}

	}

	private static ZoneState preForSimpleAction(final ZoneState state, final SimpleXtaAction asSimple,
			final ZonePrec prec) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	private static ZoneState preForSyncedAction(final ZoneState state, final SyncedXtaAction asSynced,
			final ZonePrec prec) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
