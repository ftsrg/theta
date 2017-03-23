package hu.bme.mit.theta.analysis.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SyncedXtaAction;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.BoolLitExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.ta.utils.impl.TaUtils;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

final class XtaTransferFunction<S extends State, P extends Prec>
		implements TransferFunction<XtaState<S>, XtaAction, P> {

	private final TransferFunction<S, ? super SimpleXtaAction, ? super P> transferFunction;

	private XtaTransferFunction(final TransferFunction<S, ? super SimpleXtaAction, ? super P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <S extends State, P extends Prec> XtaTransferFunction<S, P> create(
			final TransferFunction<S, ? super SimpleXtaAction, ? super P> transferFunction) {
		return new XtaTransferFunction<>(transferFunction);
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

		final List<Loc> succLocs = action.getTargetLocs();
		final Valuation succVal = createSuccValForSimpleAction(val, edge);
		if (succVal == null) {
			return Collections.emptySet();
		}
		final Collection<? extends S> succStates = transferFunction.getSuccStates(state, action, prec);

		return XtaState.collectionOf(succLocs, succVal, succStates);
	}

	private static Valuation createSuccValForSimpleAction(final Valuation val, final Edge edge) {
		for (final Expr<BoolType> guard : edge.getGuards()) {
			if (TaUtils.isDataExpr(guard)) {
				final BoolLitExpr value = (BoolLitExpr) ExprUtils.evaluate(guard, val);
				if (!value.getValue()) {
					return null;
				}
			}
		}

		final Valuation.Builder builder = val.transform();

		final List<AssignStmt<?, ?>> updates = edge.getUpdates();
		for (final AssignStmt<?, ?> update : updates) {
			if (TaUtils.isDataStmt(update)) {
				final VarDecl<?> varDecl = update.getVarDecl();
				final Expr<?> expr = update.getExpr();
				final LitExpr<?> value = ExprUtils.evaluate(expr, builder);
				builder.put(varDecl, value);
			}
		}

		return builder.build();
	}

	private Collection<XtaState<S>> getSuccStatesForSyncedAction(final XtaState<S> state, final SyncedXtaAction action,
			final P prec) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
