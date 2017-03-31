package hu.bme.mit.theta.analysis.xta.algorithm.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SyncedXtaAction;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.xta.algorithm.itp.XtaItpStatistics;
import hu.bme.mit.theta.analysis.zone.lu.BoundFunction;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.op.ResetOp;
import hu.bme.mit.theta.formalism.ta.utils.impl.TaExpr;
import hu.bme.mit.theta.formalism.ta.utils.impl.TaStmt;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaLuRefiner {

	private final Waitlist<ArgNode<XtaState<LuZoneState>, XtaAction>> waitlist;
	private final XtaItpStatistics.Builder statisticsBuilder;

	private XtaLuRefiner(final XtaSystem system, final Waitlist<ArgNode<XtaState<LuZoneState>, XtaAction>> waitlist,
			final XtaItpStatistics.Builder statisticsBuilder) {
		checkNotNull(system);
		this.waitlist = checkNotNull(waitlist);
		this.statisticsBuilder = checkNotNull(statisticsBuilder);
	}

	public static XtaLuRefiner create(final XtaSystem system,
			final Waitlist<ArgNode<XtaState<LuZoneState>, XtaAction>> waitlist,
			final XtaItpStatistics.Builder statisticsBuilder) {
		return new XtaLuRefiner(system, waitlist, statisticsBuilder);
	}

	public void refine(final ArgNode<XtaState<LuZoneState>, XtaAction> node, final BoundFunction boundFunction) {
		statisticsBuilder.startRefinement();
		propagateBounds(node, boundFunction);
		statisticsBuilder.stopRefinement();
	}

	private void propagateBounds(final ArgNode<XtaState<LuZoneState>, XtaAction> node,
			final BoundFunction boundFunction) {

		statisticsBuilder.refine();

		refineNode(node, boundFunction);
		maintainCoverage(node);

		if (node.getInEdge().isPresent()) {
			final ArgEdge<XtaState<LuZoneState>, XtaAction> inEdge = node.getInEdge().get();
			final XtaAction action = inEdge.getAction();
			final ArgNode<XtaState<LuZoneState>, XtaAction> parent = inEdge.getSource();

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

			propagateBounds(parent, builder.build());
		}
	}

	private void refineNode(final ArgNode<XtaState<LuZoneState>, XtaAction> node, final BoundFunction boundFunction) {
		final BoundFunction oldBoundFunction = node.getState().getState().getBoundFunction();
		final BoundFunction newBoundFunction = BoundFunction.max(oldBoundFunction, boundFunction);
		final LuZoneState newItpState = node.getState().getState().withBoundFunction(newBoundFunction);
		node.setState(node.getState().withState(newItpState));
	}

	private void maintainCoverage(final ArgNode<XtaState<LuZoneState>, XtaAction> node) {
		waitlist.addAll(node.getCoveredNodes());
		node.clearCoveredNodes();
	}

}
