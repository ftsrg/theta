package hu.bme.mit.theta.analysis.xta.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
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

		final List<Loc> sourceLocs = action.getSourceLocs();
		final Edge edge = action.getEdge();
		final List<Loc> targetLocs = action.getTargetLocs();

		applyInvariants(succStateBuilder, sourceLocs);
		applyGuards(succStateBuilder, edge);
		applyUpdates(succStateBuilder, edge);
		applyInvariants(succStateBuilder, targetLocs);
		if (shouldApplyDelay(action.getTargetLocs())) {
			applyDelay(succStateBuilder);
		}

		final ZoneState succState = succStateBuilder.build();
		return succState;
	}

	private static boolean shouldApplyDelay(final List<Loc> locs) {
		return locs.stream().allMatch(l -> l.getKind() == Kind.NORMAL);
	}

	private static ZoneState postForSyncedAction(final ZoneState state, final SyncedXtaAction action,
			final ZonePrec prec) {
		final ZoneState.Builder succStateBuilder = state.project(prec.getClocks());

		final List<Loc> sourceLocs = action.getSourceLocs();
		final Edge emittingEdge = action.getEmittingEdge();
		final Edge receivingEdge = action.getReceivingEdge();
		final List<Loc> targetLocs = action.getTargetLocs();

		applyInvariants(succStateBuilder, sourceLocs);
		applyGuards(succStateBuilder, emittingEdge);
		applyGuards(succStateBuilder, receivingEdge);
		applyUpdates(succStateBuilder, emittingEdge);
		applyUpdates(succStateBuilder, receivingEdge);
		applyInvariants(succStateBuilder, targetLocs);

		if (shouldApplyDelay(targetLocs)) {
			applyDelay(succStateBuilder);
		}

		final ZoneState succState = succStateBuilder.build();
		return succState;
	}

	private static void applyDelay(final ZoneState.Builder succStateBuilder) {
		succStateBuilder.up();
	}

	private static void applyInvariants(final ZoneState.Builder succStateBuilder, final Collection<Loc> locs) {
		for (final Loc target : locs) {
			for (final Expr<BoolType> invar : target.getInvars()) {
				final TaExpr expr = TaExpr.of(invar);
				if (expr.isClockExpr()) {
					succStateBuilder.and(expr.asClockExpr().getClockConstr());
				}
			}
		}
	}

	private static void applyUpdates(final ZoneState.Builder succStateBuilder, final Edge emittingEdge) {
		for (final AssignStmt<?, ?> update : emittingEdge.getUpdates()) {
			final TaStmt stmt = TaStmt.of(update);
			if (stmt.isClockStmt()) {
				succStateBuilder.execute(stmt.asClockStmt().getClockOp());
			}
		}
	}

	private static void applyGuards(final ZoneState.Builder succStateBuilder, final Edge emittingEdge) {
		for (final Expr<BoolType> guard : emittingEdge.getGuards()) {
			final TaExpr expr = TaExpr.of(guard);
			if (expr.isClockExpr()) {
				succStateBuilder.and(expr.asClockExpr().getClockConstr());
			}
		}
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
