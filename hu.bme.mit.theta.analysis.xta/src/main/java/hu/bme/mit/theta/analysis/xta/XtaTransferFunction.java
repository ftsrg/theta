package hu.bme.mit.theta.analysis.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.emptySet;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SimpleXtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAction.SyncedXtaAction;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.formalism.xta.Guard;
import hu.bme.mit.theta.formalism.xta.Update;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

final class XtaTransferFunction<S extends State, P extends Prec>
		implements TransferFunction<XtaState<S>, XtaAction, P> {

	private final TransferFunction<S, ? super XtaAction, ? super P> transferFunction;

	private XtaTransferFunction(final TransferFunction<S, ? super XtaAction, ? super P> transferFunction) {
		this.transferFunction = checkNotNull(transferFunction);
	}

	public static <S extends State, P extends Prec> XtaTransferFunction<S, P> create(
			final TransferFunction<S, ? super XtaAction, ? super P> transferFunction) {
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

		if (!checkDataGuards(edge, val)) {
			return emptySet();
		}

		final List<Loc> succLocs = action.getTargetLocs();
		final Valuation succVal = createSuccValForSimpleAction(val, action);
		final Collection<? extends S> succStates = transferFunction.getSuccStates(state, action, prec);

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
		final Collection<? extends S> succStates = transferFunction.getSuccStates(state, action, prec);

		return XtaState.collectionOf(succLocs, succVal, succStates);
	}

	private static Valuation createSuccValForSimpleAction(final Valuation val, final SimpleXtaAction action) {
		final Valuation.Builder builder = val.transform();
		applyDataUpdates(action.getEdge(), builder);
		return builder.build();
	}

	private Valuation createSuccValForSyncedAction(final Valuation val, final SyncedXtaAction action) {
		final Valuation.Builder builder = val.transform();
		applyDataUpdates(action.getEmittingEdge(), builder);
		applyDataUpdates(action.getReceivingEdge(), builder);
		return builder.build();
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

	private static void applyDataUpdates(final Edge edge, final Valuation.Builder builder) {
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
