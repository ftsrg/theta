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
package hu.bme.mit.theta.xta.analysis.lazy;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static com.google.common.collect.Streams.zip;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

import com.google.common.collect.Lists;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.WpState;
import hu.bme.mit.theta.xta.Guard;
import hu.bme.mit.theta.xta.Update;
import hu.bme.mit.theta.xta.XtaProcess.Edge;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.BasicXtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAction.SyncedXtaAction;

public final class XtaDataUtils {

	private XtaDataUtils() {
	}

	public static Valuation interpolate(final Valuation valA, final Expr<BoolType> exprB) {
		final Collection<VarDecl<?>> vars = ExprUtils.getVars(exprB);
		final MutableValuation valI = new MutableValuation();
		for (final VarDecl<?> var : vars) {
			final LitExpr<?> val = valA.eval(var).get();
			valI.put(var, val);
		}

		assert ExprUtils.simplify(exprB, valI).equals(False());

		for (final VarDecl<?> var : vars) {
			valI.remove(var);
			final Expr<BoolType> simplifiedExprB = ExprUtils.simplify(exprB, valI);
			if (simplifiedExprB.equals(False())) {
				continue;
			} else {
				final LitExpr<?> val = valA.eval(var).get();
				valI.put(var, val);
			}
		}

		return valI;
	}

	public static Expr<BoolType> pre(final Expr<BoolType> expr, final XtaAction action) {
		checkNotNull(expr);
		checkNotNull(action);

		if (action.isBasic()) {
			return preForSimpleAction(expr, action.asBasic());
		} else if (action.isSynced()) {
			return preForSyncedAction(expr, action.asSynced());
		} else {
			throw new AssertionError();
		}
	}

	private static Expr<BoolType> preForSimpleAction(final Expr<BoolType> expr, final BasicXtaAction action) {
		final Edge edge = action.getEdge();
		final WpState wp0 = WpState.of(expr);
		final WpState wp1 = applyInverseUpdates(wp0, edge);
		final WpState wp2 = applyGuards(wp1, edge);
		return wp2.getExpr();
	}

	private static Expr<BoolType> preForSyncedAction(final Expr<BoolType> expr, final SyncedXtaAction action) {
		final Edge emitEdge = action.getEmitEdge();
		final Edge recvEdge = action.getRecvEdge();
		final WpState wp0 = WpState.of(expr);
		final WpState wp1 = applyInverseUpdates(wp0, recvEdge);
		final WpState wp2 = applyInverseUpdates(wp1, emitEdge);
		final WpState wp3 = applyGuards(wp2, recvEdge);
		final WpState wp4 = applyGuards(wp3, emitEdge);
		final WpState wp5 = applySync(wp4, emitEdge, recvEdge);
		return wp5.getExpr();
	}

	private static WpState applyInverseUpdates(final WpState state, final Edge edge) {
		WpState res = state;
		for (final Update update : Lists.reverse(edge.getUpdates())) {
			if (update.isDataUpdate()) {
				res = res.wep(update.asDataUpdate().toStmt());
			}
		}
		return res;
	}

	private static WpState applyGuards(final WpState state, final Edge edge) {
		WpState res = state;
		for (final Guard guard : edge.getGuards()) {
			if (guard.isDataGuard()) {
				res = res.wep(Assume(guard.asDataGuard().toExpr()));
			}
		}
		return res;
	}

	private static WpState applySync(final WpState state, final Edge emitEdge, final Edge recvEdge) {
		final Stream<Expr<?>> emitArgs = emitEdge.getSync().get().getArgs().stream();
		final Stream<Expr<?>> recvArgs = recvEdge.getSync().get().getArgs().stream();
		final List<Expr<BoolType>> exprs = zip(emitArgs, recvArgs, (e, r) -> (Expr<BoolType>) Eq(e, r))
				.collect(toImmutableList());
		final Expr<BoolType> andExpr = And(exprs);
		return state.wep(Assume(andExpr));
	}

}
