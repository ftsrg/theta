package hu.bme.mit.theta.analysis.xta.zone;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SyncedXtaAction;
import hu.bme.mit.theta.analysis.zone.BoundFunction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.op.ResetOp;
import hu.bme.mit.theta.formalism.ta.utils.impl.TaExpr;
import hu.bme.mit.theta.formalism.ta.utils.impl.TaStmt;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

public final class XtaLuZoneUtils {

	private XtaLuZoneUtils() {
	}

	public static BoundFunction pre(final BoundFunction boundFunction, final XtaAction action) {
		final BoundFunction.Builder builder = boundFunction.transform();

		final List<Loc> sourceLocs = action.getSourceLocs();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (action.isSimple()) {
			final SimpleXtaAction simpleAction = action.asSimple();

			final List<AssignStmt<?, ?>> updates = simpleAction.getEdge().getUpdates();
			final Collection<Expr<BoolType>> guards = simpleAction.getEdge().getGuards();

			for (final Loc loc : targetLocs) {
				for (final Expr<BoolType> invar : loc.getInvars()) {
					final TaExpr expr = TaExpr.of(invar);
					if (expr.isClockExpr()) {
						builder.add(expr.asClockExpr().getClockConstr());
					}
				}
			}

			for (final AssignStmt<?, ?> update : updates) {
				final TaStmt stmt = TaStmt.of(update);
				if (stmt.isClockStmt()) {
					final ResetOp op = (ResetOp) stmt.asClockStmt().getClockOp();
					final ClockDecl clock = op.getClock();
					builder.remove(clock);
				}
			}

			for (final Expr<BoolType> guard : guards) {
				final TaExpr expr = TaExpr.of(guard);
				if (expr.isClockExpr()) {
					builder.add(expr.asClockExpr().getClockConstr());
				}
			}

			for (final Loc loc : sourceLocs) {
				for (final Expr<BoolType> invar : loc.getInvars()) {
					final TaExpr expr = TaExpr.of(invar);
					if (expr.isClockExpr()) {
						builder.add(expr.asClockExpr().getClockConstr());
					}
				}
			}

		} else if (action.isSynced()) {

			final SyncedXtaAction syncedAction = action.asSynced();

			final Edge emittingEdge = syncedAction.getEmittingEdge();
			final Edge receivingEdge = syncedAction.getReceivingEdge();

			for (final Loc loc : targetLocs) {
				for (final Expr<BoolType> invar : loc.getInvars()) {
					final TaExpr expr = TaExpr.of(invar);
					if (expr.isClockExpr()) {
						builder.add(expr.asClockExpr().getClockConstr());
					}
				}
			}

			for (final AssignStmt<?, ?> update : receivingEdge.getUpdates()) {
				final TaStmt stmt = TaStmt.of(update);
				if (stmt.isClockStmt()) {
					final ResetOp op = (ResetOp) stmt.asClockStmt().getClockOp();
					final ClockDecl clock = op.getClock();
					builder.remove(clock);
				}
			}

			for (final AssignStmt<?, ?> update : emittingEdge.getUpdates()) {
				final TaStmt stmt = TaStmt.of(update);
				if (stmt.isClockStmt()) {
					final ResetOp op = (ResetOp) stmt.asClockStmt().getClockOp();
					final ClockDecl clock = op.getClock();
					builder.remove(clock);
				}
			}

			for (final Expr<BoolType> guard : receivingEdge.getGuards()) {
				final TaExpr expr = TaExpr.of(guard);
				if (expr.isClockExpr()) {
					builder.add(expr.asClockExpr().getClockConstr());
				}
			}

			for (final Expr<BoolType> guard : emittingEdge.getGuards()) {
				final TaExpr expr = TaExpr.of(guard);
				if (expr.isClockExpr()) {
					builder.add(expr.asClockExpr().getClockConstr());
				}
			}

			for (final Loc loc : sourceLocs) {
				for (final Expr<BoolType> invar : loc.getInvars()) {
					final TaExpr expr = TaExpr.of(invar);
					if (expr.isClockExpr()) {
						builder.add(expr.asClockExpr().getClockConstr());
					}
				}
			}
		} else {
			throw new AssertionError();
		}

		return builder.build();
	}

}
