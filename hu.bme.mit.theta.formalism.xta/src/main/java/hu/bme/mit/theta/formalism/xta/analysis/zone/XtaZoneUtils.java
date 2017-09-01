package hu.bme.mit.theta.formalism.xta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.clock.constr.ClockConstrs.Eq;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.Lists;

import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.clock.op.ResetOp;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.Guard;
import hu.bme.mit.theta.formalism.xta.Update;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaProcess.LocKind;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction.SyncedXtaAction;

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
		final ZoneState.Builder succStateBuilder = state.project(prec.getVars());

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

	private static ZoneState postForSyncedAction(final ZoneState state, final SyncedXtaAction action,
			final ZonePrec prec) {
		final ZoneState.Builder succStateBuilder = state.project(prec.getVars());

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

	////

	public static ZoneState pre(final ZoneState state, final XtaAction action, final ZonePrec prec) {
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

	private static ZoneState preForSimpleAction(final ZoneState state, final SimpleXtaAction action,
			final ZonePrec prec) {
		final ZoneState.Builder preStateBuilder = state.project(prec.getVars());

		final List<Loc> sourceLocs = action.getSourceLocs();
		final Edge edge = action.getEdge();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (shouldApplyDelay(action.getTargetLocs())) {
			applyInverseDelay(preStateBuilder);
		}
		applyInvariants(preStateBuilder, targetLocs);
		applyInverseUpdates(preStateBuilder, edge);
		applyGuards(preStateBuilder, edge);
		applyInvariants(preStateBuilder, sourceLocs);

		final ZoneState preState = preStateBuilder.build();
		return preState;
	}

	private static ZoneState preForSyncedAction(final ZoneState state, final SyncedXtaAction action,
			final ZonePrec prec) {
		final ZoneState.Builder preStateBuilder = state.project(prec.getVars());

		final List<Loc> sourceLocs = action.getSourceLocs();
		final Edge emittingEdge = action.getEmittingEdge();
		final Edge receivingEdge = action.getReceivingEdge();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (shouldApplyDelay(action.getTargetLocs())) {
			applyInverseDelay(preStateBuilder);
		}
		applyInvariants(preStateBuilder, targetLocs);
		applyInverseUpdates(preStateBuilder, receivingEdge);
		applyInverseUpdates(preStateBuilder, emittingEdge);
		applyGuards(preStateBuilder, receivingEdge);
		applyGuards(preStateBuilder, emittingEdge);
		applyInvariants(preStateBuilder, sourceLocs);

		final ZoneState succState = preStateBuilder.build();
		return succState;
	}

	private static void applyInverseDelay(final ZoneState.Builder builder) {
		builder.down();
		builder.nonnegative();
	}

	////

	private static boolean shouldApplyDelay(final List<Loc> locs) {
		return locs.stream().allMatch(l -> l.getKind() == LocKind.NORMAL);
	}

	private static void applyDelay(final ZoneState.Builder builder) {
		builder.nonnegative();
		builder.up();
	}

	private static void applyInvariants(final ZoneState.Builder builder, final Collection<Loc> locs) {
		for (final Loc target : locs) {
			for (final Guard invar : target.getInvars()) {
				if (invar.isClockGuard()) {
					builder.and(invar.asClockGuard().getClockConstr());
				}
			}
		}
	}

	private static void applyUpdates(final ZoneState.Builder builder, final Edge edge) {
		for (final Update update : edge.getUpdates()) {
			if (update.isClockUpdate()) {
				final ResetOp op = (ResetOp) update.asClockUpdate().getClockOp();
				final VarDecl<RatType> var = op.getVar();
				final int value = op.getValue();
				builder.reset(var, value);
			}
		}
	}

	private static void applyInverseUpdates(final ZoneState.Builder builder, final Edge edge) {
		for (final Update update : Lists.reverse(edge.getUpdates())) {
			if (update.isClockUpdate()) {
				final ResetOp op = (ResetOp) update.asClockUpdate().getClockOp();
				final VarDecl<RatType> var = op.getVar();
				final int value = op.getValue();
				builder.and(Eq(var, value));
				builder.free(var);
			}
		}
	}

	private static void applyGuards(final ZoneState.Builder builder, final Edge edge) {
		for (final Guard guard : edge.getGuards()) {
			if (guard.isClockGuard()) {
				builder.and(guard.asClockGuard().getClockConstr());
			}
		}
	}

}
