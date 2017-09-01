package hu.bme.mit.theta.formalism.xta.analysis.zone;

import java.util.List;

import hu.bme.mit.theta.analysis.zone.BoundFunction;
import hu.bme.mit.theta.core.clock.op.ResetOp;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.Guard;
import hu.bme.mit.theta.formalism.xta.Update;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction.SyncedXtaAction;

public final class XtaLuZoneUtils {

	private XtaLuZoneUtils() {
	}

	public static BoundFunction pre(final BoundFunction boundFunction, final XtaAction action) {
		if (action.isSimple()) {
			return preForSimpleAction(boundFunction, action.asSimple());
		} else if (action.isSynced()) {
			return preForSyncedAction(boundFunction, action.asSynced());
		} else {
			throw new AssertionError();
		}
	}

	////

	private static BoundFunction preForSimpleAction(final BoundFunction boundFunction, final SimpleXtaAction action) {
		final BoundFunction.Builder succStateBuilder = boundFunction.transform();

		final List<Loc> sourceLocs = action.getSourceLocs();
		final List<Loc> targetLocs = action.getTargetLocs();
		final Edge edge = action.getEdge();

		applyInvariants(succStateBuilder, targetLocs);
		applyInverseUpdates(succStateBuilder, edge);
		applyGuards(succStateBuilder, edge);
		applyInvariants(succStateBuilder, sourceLocs);
		return succStateBuilder.build();
	}

	private static BoundFunction preForSyncedAction(final BoundFunction boundFunction, final SyncedXtaAction action) {
		final BoundFunction.Builder succStateBuilder = boundFunction.transform();

		final List<Loc> sourceLocs = action.getSourceLocs();
		final List<Loc> targetLocs = action.getTargetLocs();
		final Edge emittingEdge = action.getEmittingEdge();
		final Edge receivingEdge = action.getReceivingEdge();

		applyInvariants(succStateBuilder, targetLocs);
		applyInverseUpdates(succStateBuilder, receivingEdge);
		applyInverseUpdates(succStateBuilder, emittingEdge);
		applyGuards(succStateBuilder, receivingEdge);
		applyGuards(succStateBuilder, emittingEdge);
		applyInvariants(succStateBuilder, sourceLocs);
		return succStateBuilder.build();
	}

	////

	private static void applyInverseUpdates(final BoundFunction.Builder succStateBuilder, final Edge edge) {
		for (final Update update : edge.getUpdates()) {
			if (update.isClockUpdate()) {
				final ResetOp op = (ResetOp) update.asClockUpdate().getClockOp();
				final VarDecl<RatType> var = op.getVar();
				succStateBuilder.remove(var);
			}
		}
	}

	private static void applyGuards(final BoundFunction.Builder succStateBuilder, final Edge edge) {
		for (final Guard guard : edge.getGuards()) {
			if (guard.isClockGuard()) {
				succStateBuilder.add(guard.asClockGuard().getClockConstr());
			}
		}
	}

	private static void applyInvariants(final BoundFunction.Builder succStateBuilder, final List<Loc> targetLocs) {
		for (final Loc loc : targetLocs) {
			for (final Guard invar : loc.getInvars()) {
				if (invar.isClockGuard()) {
					succStateBuilder.add(invar.asClockGuard().getClockConstr());
				}
			}
		}
	}

}
