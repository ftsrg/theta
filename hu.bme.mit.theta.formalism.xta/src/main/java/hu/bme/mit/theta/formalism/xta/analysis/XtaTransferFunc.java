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
package hu.bme.mit.theta.formalism.xta.analysis;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.emptySet;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.BasicValuation;
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
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction.SyncedXtaAction;

final class XtaTransferFunc<S extends State, P extends Prec> implements TransferFunc<XtaState<S>, XtaAction, P> {

	private final TransferFunc<S, ? super XtaAction, ? super P> transferFunc;

	private XtaTransferFunc(final TransferFunc<S, ? super XtaAction, ? super P> transferFunc) {
		this.transferFunc = checkNotNull(transferFunc);
	}

	public static <S extends State, P extends Prec> XtaTransferFunc<S, P> create(
			final TransferFunc<S, ? super XtaAction, ? super P> transferFunc) {
		return new XtaTransferFunc<>(transferFunc);
	}

	@Override
	public Collection<XtaState<S>> getSuccStates(final XtaState<S> state, final XtaAction action, final P prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		if (action.isSimple()) {
			return getSuccStatesForSimpleAction(state, action.asSimple(), prec);
		} else if (action.isSynced()) {
			return getSuccStatesForSyncedAction(state, action.asSynced(), prec);
		} else {
			throw new AssertionError();
		}
	}

	private Collection<XtaState<S>> getSuccStatesForSimpleAction(final XtaState<S> xtaState,
			final SimpleXtaAction action, final P prec) {
		checkArgument(xtaState.getLocs() == action.getSourceLocs());

		final Edge edge = action.getEdge();
		final Valuation val = xtaState.getVal();
		final S state = xtaState.getState();

		if (!checkDataGuards(edge, val)) {
			return emptySet();
		}

		final List<Loc> succLocs = action.getTargetLocs();
		final Valuation succVal = createSuccValForSimpleAction(val, action);
		final Collection<? extends S> succStates = transferFunc.getSuccStates(state, action, prec);

		return XtaState.collectionOf(succLocs, succVal, succStates);
	}

	private Collection<XtaState<S>> getSuccStatesForSyncedAction(final XtaState<S> xtaState,
			final SyncedXtaAction action, final P prec) {
		checkArgument(xtaState.getLocs() == action.getSourceLocs());

		final Edge emittingEdge = action.getEmittingEdge();
		final Edge receivingEdge = action.getReceivingEdge();
		final Valuation val = xtaState.getVal();
		final S state = xtaState.getState();

		if (!checkDataGuards(emittingEdge, val)) {
			return emptySet();
		}

		if (!checkDataGuards(receivingEdge, val)) {
			return emptySet();
		}

		final List<Loc> succLocs = action.getTargetLocs();
		final Valuation succVal = createSuccValForSyncedAction(val, action);
		final Collection<? extends S> succStates = transferFunc.getSuccStates(state, action, prec);

		return XtaState.collectionOf(succLocs, succVal, succStates);
	}

	private static Valuation createSuccValForSimpleAction(final Valuation val, final SimpleXtaAction action) {
		final MutableValuation builder = MutableValuation.copyOf(val);
		applyDataUpdates(action.getEdge(), builder);
		return BasicValuation.copyOf(builder);
	}

	private Valuation createSuccValForSyncedAction(final Valuation val, final SyncedXtaAction action) {
		final MutableValuation builder = MutableValuation.copyOf(val);
		applyDataUpdates(action.getEmittingEdge(), builder);
		applyDataUpdates(action.getReceivingEdge(), builder);
		return BasicValuation.copyOf(builder);
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
