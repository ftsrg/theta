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

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.core.clock.op.ResetOp;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xta.Guard;
import hu.bme.mit.theta.xta.Update;
import hu.bme.mit.theta.xta.XtaProcess.Edge;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BasicXtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BinaryXtaAction;

public final class XtaActZoneUtils {

	private XtaActZoneUtils() {
	}

	public static Set<VarDecl<RatType>> pre(final Set<VarDecl<RatType>> activeVars, final XtaAction action) {
		final Set<VarDecl<RatType>> result = new HashSet<>();

		final List<Loc> sourceLocs = action.getSourceLocs();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (action.isBasic()) {
			final BasicXtaAction basicAction = action.asBasic();

			final List<Update> updates = basicAction.getEdge().getUpdates();
			final Collection<Guard> guards = basicAction.getEdge().getGuards();

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
					final VarDecl<RatType> varDecl = op.getVar();
					result.remove(varDecl);
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

		} else if (action.isBinary()) {

			final BinaryXtaAction binaryAction = action.asBinary();

			final Edge emittingEdge = binaryAction.getEmitEdge();
			final Edge receivingEdge = binaryAction.getRecvEdge();

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
					final VarDecl<RatType> varDecl = op.getVar();
					result.remove(varDecl);
				}
			}

			for (final Update update : emittingEdge.getUpdates()) {
				if (update.isClockUpdate()) {
					final ResetOp op = (ResetOp) update.asClockUpdate().getClockOp();
					final VarDecl<RatType> varDecl = op.getVar();
					result.remove(varDecl);
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
