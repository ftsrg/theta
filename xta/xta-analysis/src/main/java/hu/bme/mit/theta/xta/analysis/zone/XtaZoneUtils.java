/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xta.analysis.zone;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.clock.op.ResetOp;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xta.Guard;
import hu.bme.mit.theta.xta.Update;
import hu.bme.mit.theta.xta.XtaProcess.Edge;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.XtaProcess.LocKind;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BasicXtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BinaryXtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BroadcastXtaAction;

import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.clock.constr.ClockConstrs.Eq;

public final class XtaZoneUtils {

	private XtaZoneUtils() {
	}

	public static ZoneState post(final ZoneState state, final XtaAction action, final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		if (action.isBasic()) {
			return postForBasicAction(state, action.asBasic(), prec);
		} else if (action.isBinary()) {
			return postForBinaryAction(state, action.asBinary(), prec);
		} else if (action.isBroadcast()) {
			return postForBroadcastAction(state, action.asBroadcast(), prec);
		} else {
			throw new AssertionError();
		}
	}

	private static ZoneState postForBasicAction(final ZoneState state, final BasicXtaAction action,
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

	private static ZoneState postForBinaryAction(final ZoneState state, final BinaryXtaAction action,
												 final ZonePrec prec) {
		final ZoneState.Builder succStateBuilder = state.project(prec.getVars());

		final List<Loc> sourceLocs = action.getSourceLocs();
		final Edge emittingEdge = action.getEmitEdge();
		final Edge receivingEdge = action.getRecvEdge();
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

	private static ZoneState postForBroadcastAction(final ZoneState state, final BroadcastXtaAction action,
													final ZonePrec prec) {
		final ZoneState.Builder succStateBuilder = state.project(prec.getVars());

		final List<Loc> sourceLocs = action.getSourceLocs();
		final Edge emitEdge = action.getEmitEdge();
		final List<Edge> recvEdges = action.getRecvEdges();
		final List<Collection<Edge>> nonRecvEdgeCols = action.getNonRecvEdges();
		final List<Loc> targetLocs = action.getTargetLocs();

		applyInvariants(succStateBuilder, sourceLocs);
		applyGuards(succStateBuilder, emitEdge);

		if (recvEdges.stream().anyMatch(XtaZoneUtils::hasClockGuards)) {
			throw new UnsupportedOperationException(
					"Clock guards on edges with broadcast synchronization labels are not supported.");
		}

		if (nonRecvEdgeCols.stream().anyMatch(c -> c.stream().anyMatch(XtaZoneUtils::hasClockGuards))) {
			throw new UnsupportedOperationException(
					"Clock guards on edges with broadcast synchronization labels are not supported.");
		}

		applyUpdates(succStateBuilder, emitEdge);
		recvEdges.stream().forEachOrdered(recvEdge -> applyUpdates(succStateBuilder, recvEdge));
		applyInvariants(succStateBuilder, targetLocs);

		if (shouldApplyDelay(targetLocs)) {
			applyDelay(succStateBuilder);
		}

		final ZoneState succState = succStateBuilder.build();
		return succState;
	}

	private static boolean hasClockGuards(Edge edge) {
		return edge.getGuards().stream().anyMatch(Guard::isClockGuard);
	}

	////

	public static ZoneState pre(final ZoneState state, final XtaAction action, final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		if (action.isBasic()) {
			return preForBasicAction(state, action.asBasic(), prec);
		} else if (action.isBinary()) {
			return preForBinaryAction(state, action.asBinary(), prec);
		} else if (action.isBroadcast()) {
			return preForBroadcastAction(state, action.asBroadcast(), prec);
		} else {
			throw new AssertionError();
		}
	}

	private static ZoneState preForBasicAction(final ZoneState state, final BasicXtaAction action,
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

	private static ZoneState preForBinaryAction(final ZoneState state, final BinaryXtaAction action,
												final ZonePrec prec) {
		final ZoneState.Builder preStateBuilder = state.project(prec.getVars());

		final List<Loc> sourceLocs = action.getSourceLocs();
		final Edge emitEdge = action.getEmitEdge();
		final Edge recvEdge = action.getRecvEdge();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (shouldApplyDelay(action.getTargetLocs())) {
			applyInverseDelay(preStateBuilder);
		}
		applyInvariants(preStateBuilder, targetLocs);
		applyInverseUpdates(preStateBuilder, recvEdge);
		applyInverseUpdates(preStateBuilder, emitEdge);
		applyGuards(preStateBuilder, recvEdge);
		applyGuards(preStateBuilder, emitEdge);
		applyInvariants(preStateBuilder, sourceLocs);

		final ZoneState succState = preStateBuilder.build();
		return succState;
	}

	private static ZoneState preForBroadcastAction(final ZoneState state, final BroadcastXtaAction action,
												   final ZonePrec prec) {
		final ZoneState.Builder preStateBuilder = state.project(prec.getVars());

		final List<Loc> sourceLocs = action.getSourceLocs();
		final Edge emitEdge = action.getEmitEdge();
		final List<Edge> reverseRecvEdges = Lists.reverse(action.getRecvEdges());
		final List<Collection<Edge>> nonRecvEdgeCols = action.getNonRecvEdges();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (shouldApplyDelay(action.getTargetLocs())) {
			applyInverseDelay(preStateBuilder);
		}
		applyInvariants(preStateBuilder, targetLocs);
		reverseRecvEdges.stream().forEachOrdered(recvEdge -> applyInverseUpdates(preStateBuilder, recvEdge));
		applyInverseUpdates(preStateBuilder, emitEdge);

		if (nonRecvEdgeCols.stream().anyMatch(c -> c.stream().anyMatch(XtaZoneUtils::hasClockGuards))) {
			throw new UnsupportedOperationException(
					"Clock guards on edges with broadcast synchronization labels are not supported.");
		}

		if (reverseRecvEdges.stream().anyMatch(XtaZoneUtils::hasClockGuards)) {
			throw new UnsupportedOperationException(
					"Clock guards on edges with broadcast synchronization labels are not supported.");
		}

		applyGuards(preStateBuilder, emitEdge);
		applyInvariants(preStateBuilder, sourceLocs);

		final ZoneState succState = preStateBuilder.build();
		return succState;
	}

	////

	private static boolean shouldApplyDelay(final List<Loc> locs) {
		return locs.stream().allMatch(l -> l.getKind() == LocKind.NORMAL);
	}

	private static void applyDelay(final ZoneState.Builder builder) {
		builder.nonnegative();
		builder.up();
	}

	private static void applyInverseDelay(final ZoneState.Builder builder) {
		builder.down();
		builder.nonnegative();
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
				final VarDecl<RatType> varDecl = op.getVar();
				final int value = op.getValue();
				builder.reset(varDecl, value);
			}
		}
	}

	private static void applyInverseUpdates(final ZoneState.Builder builder, final Edge edge) {
		for (final Update update : Lists.reverse(edge.getUpdates())) {
			if (update.isClockUpdate()) {
				final ResetOp op = (ResetOp) update.asClockUpdate().getClockOp();
				final VarDecl<RatType> varDecl = op.getVar();
				final int value = op.getValue();
				builder.and(Eq(varDecl, value));
				builder.free(varDecl);
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
