package hu.bme.mit.theta.analysis.xta.zone;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SyncedXtaAction;
import hu.bme.mit.theta.core.clock.op.ResetOp;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.Guard;
import hu.bme.mit.theta.formalism.xta.Update;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

public final class XtaActZoneUtils {

	private XtaActZoneUtils() {
	}

	public static Set<VarDecl<RatType>> pre(final Set<VarDecl<RatType>> activeVars, final XtaAction action) {
		final Set<VarDecl<RatType>> result = new HashSet<>();

		final List<Loc> sourceLocs = action.getSourceLocs();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (action.isSimple()) {
			final SimpleXtaAction simpleAction = action.asSimple();

			final List<Update> updates = simpleAction.getEdge().getUpdates();
			final Collection<Guard> guards = simpleAction.getEdge().getGuards();

			for (final Loc loc : targetLocs) {
				for (final Guard invar : loc.getInvars()) {
					if (invar.isClockGuard()) {
						result.addAll(invar.asClockGuard().getClockConstr().getVars());
					}
				}
			}

			for (final Update update : updates) {
				if (update.isClockUpdate()) {
					final ResetOp op = (ResetOp) update.asClockUpdate().getClockOp();
					final VarDecl<RatType> var = op.getVar();
					result.remove(var);
				}
			}

			for (final Guard guard : guards) {
				if (guard.isClockGuard()) {
					result.addAll(guard.asClockGuard().getClockConstr().getVars());
				}
			}

			for (final Loc loc : sourceLocs) {
				for (final Guard invar : loc.getInvars()) {
					if (invar.isClockGuard()) {
						result.addAll(invar.asClockGuard().getClockConstr().getVars());
					}
				}
			}

		} else if (action.isSynced()) {

			final SyncedXtaAction syncedAction = action.asSynced();

			final Edge emittingEdge = syncedAction.getEmittingEdge();
			final Edge receivingEdge = syncedAction.getReceivingEdge();

			for (final Loc loc : targetLocs) {
				for (final Guard invar : loc.getInvars()) {
					if (invar.isClockGuard()) {
						result.addAll(invar.asClockGuard().getClockConstr().getVars());
					}
				}
			}

			for (final Update update : receivingEdge.getUpdates()) {
				if (update.isClockUpdate()) {
					final ResetOp op = (ResetOp) update.asClockUpdate().getClockOp();
					final VarDecl<RatType> var = op.getVar();
					result.remove(var);
				}
			}

			for (final Update update : emittingEdge.getUpdates()) {
				if (update.isClockUpdate()) {
					final ResetOp op = (ResetOp) update.asClockUpdate().getClockOp();
					final VarDecl<RatType> var = op.getVar();
					result.remove(var);
				}
			}

			for (final Guard guard : receivingEdge.getGuards()) {
				if (guard.isClockGuard()) {
					result.addAll(guard.asClockGuard().getClockConstr().getVars());
				}
			}

			for (final Guard guard : emittingEdge.getGuards()) {
				if (guard.isClockGuard()) {
					result.addAll(guard.asClockGuard().getClockConstr().getVars());
				}
			}

			for (final Loc loc : sourceLocs) {
				for (final Guard invar : loc.getInvars()) {
					if (invar.isClockGuard()) {
						result.addAll(invar.asClockGuard().getClockConstr().getVars());
					}
				}
			}
		} else {
			throw new AssertionError();
		}

		return result;
	}

}
