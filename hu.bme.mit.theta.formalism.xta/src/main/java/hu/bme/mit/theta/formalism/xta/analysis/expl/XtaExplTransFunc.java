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
package hu.bme.mit.theta.formalism.xta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.Streams.zip;
import static java.util.Collections.singleton;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.formalism.xta.Guard;
import hu.bme.mit.theta.formalism.xta.Update;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction.BasicXtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction.SyncedXtaAction;

final class XtaExplTransFunc implements TransFunc<ExplState, XtaAction, UnitPrec> {

	private XtaExplTransFunc(final XtaSystem system) {
		// TODO remove parameter 'system'
		checkNotNull(system);
	}

	public static XtaExplTransFunc create(final XtaSystem system) {
		return new XtaExplTransFunc(system);
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final XtaAction action, final UnitPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		if (action.isBasic()) {
			return getSuccStatesForBasicAction(state, action.asBasic());
		} else if (action.isSynced()) {
			return getSuccStatesForSyncedAction(state, action.asSynced());
		} else {
			throw new AssertionError();
		}
	}

	private Collection<ExplState> getSuccStatesForBasicAction(final ExplState state, final BasicXtaAction action) {
		final Edge edge = action.getEdge();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (!checkDataGuards(edge, state)) {
			return singleton(ExplState.createBottom());
		}

		final ExplState succState = createSuccStateForSimpleAction(state, action);

		if (!checkDataInvariants(targetLocs, succState)) {
			return singleton(ExplState.createBottom());
		}

		return singleton(succState);
	}

	private Collection<ExplState> getSuccStatesForSyncedAction(final ExplState state, final SyncedXtaAction action) {
		final Edge emitEdge = action.getEmitEdge();
		final Edge recvEdge = action.getRecvEdge();
		final List<Loc> targetLocs = action.getTargetLocs();

		if (!checkSync(emitEdge, recvEdge, state)) {
			return singleton(ExplState.createBottom());
		}

		if (!checkDataGuards(emitEdge, state)) {
			return singleton(ExplState.createBottom());
		}

		if (!checkDataGuards(recvEdge, state)) {
			return singleton(ExplState.createBottom());
		}

		final ExplState succState = createSuccStateForSyncedAction(state, action);

		if (!checkDataInvariants(targetLocs, succState)) {
			return singleton(ExplState.createBottom());
		}

		return singleton(succState);
	}

	private boolean checkSync(final Edge emitEdge, final Edge recvEdge, final Valuation val) {
		final List<Expr<?>> emitArgs = emitEdge.getSync().get().getArgs();
		final List<Expr<?>> recvArgs = recvEdge.getSync().get().getArgs();
		return zip(emitArgs.stream(), recvArgs.stream(), (e, r) -> e.eval(val).equals(r.eval(val))).allMatch(x -> x);
	}

	private static boolean checkDataGuards(final Edge edge, final Valuation val) {
		for (final Guard guard : edge.getGuards()) {
			if (guard.isDataGuard()) {
				final BoolLitExpr value = (BoolLitExpr) guard.toExpr().eval(val);
				if (!value.getValue()) {
					return false;
				}
			}
		}
		return true;
	}

	private static boolean checkDataInvariants(final List<Loc> locs, final Valuation val) {
		for (final Loc loc : locs) {
			final Collection<Guard> invars = loc.getInvars();
			for (final Guard invar : invars) {
				if (invar.isDataGuard()) {
					final BoolLitExpr value = (BoolLitExpr) invar.toExpr().eval(val);
					if (!value.getValue()) {
						return false;
					}
				}
			}
		}
		return true;
	}

	private static ExplState createSuccStateForSimpleAction(final Valuation val, final BasicXtaAction action) {
		final MutableValuation builder = MutableValuation.copyOf(val);
		applyDataUpdates(action.getEdge(), builder);
		return ExplState.create(builder);
	}

	private ExplState createSuccStateForSyncedAction(final Valuation val, final SyncedXtaAction action) {
		final MutableValuation builder = MutableValuation.copyOf(val);
		applyDataUpdates(action.getEmitEdge(), builder);
		applyDataUpdates(action.getRecvEdge(), builder);
		return ExplState.create(builder);
	}

	private static void applyDataUpdates(final Edge edge, final MutableValuation builder) {
		final List<Update> updates = edge.getUpdates();
		for (final Update update : updates) {
			if (update.isDataUpdate()) {
				final AssignStmt<?> stmt = (AssignStmt<?>) update.toStmt();
				final VarDecl<?> varDecl = stmt.getVarDecl();
				final Expr<?> expr = stmt.getExpr();
				final LitExpr<?> value = expr.eval(builder);
				builder.put(varDecl, value);
			}
		}
	}

}
