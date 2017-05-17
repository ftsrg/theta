package hu.bme.mit.theta.analysis.xta;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.xta.ChanType;
import hu.bme.mit.theta.formalism.xta.Label;
import hu.bme.mit.theta.formalism.xta.Label.Kind;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

public final class XtaLts implements LTS<XtaState<?>, XtaAction> {

	private XtaLts() {
	}

	public static XtaLts create() {
		return new XtaLts();
	}

	@Override
	public Collection<XtaAction> getEnabledActionsFor(final XtaState<?> state) {
		final Collection<XtaAction> result = new ArrayList<>();
		for (final Loc loc : state.getLocs()) {
			for (final Edge edge : loc.getOutEdges()) {
				addActionsForEdge(result, state, edge);
			}
		}
		return result;
	}

	private static void addActionsForEdge(final Collection<XtaAction> result, final XtaState<?> state,
			final Edge edge) {
		if (edge.getLabel().isPresent()) {
			addSyncActionsForEdge(result, state, edge);
		} else {
			addSimpleActionsForEdge(result, state, edge);
		}
	}

	private static void addSyncActionsForEdge(final Collection<XtaAction> result, final XtaState<?> state,
			final Edge emitEdge) {

		final Loc emitLoc = emitEdge.getSource();
		final Label emitLabel = emitEdge.getLabel().get();
		if (emitLabel.getKind() != Kind.EMIT) {
			return;
		}

		@SuppressWarnings("unchecked")
		final Expr<ChanType> emitExpr = (Expr<ChanType>) ExprUtils.simplify(emitLabel.getExpr(), state.getVal());

		for (final Loc receiveLoc : state.getLocs()) {
			if (receiveLoc == emitLoc) {
				continue;
			}

			for (final Edge recieveEdge : receiveLoc.getOutEdges()) {
				if (!recieveEdge.getLabel().isPresent()) {
					continue;
				}

				final Label receiveLabel = recieveEdge.getLabel().get();
				if (receiveLabel.getKind() != Kind.RECEIVE) {
					continue;
				}

				final Expr<?> receiveExpr = ExprUtils.simplify(receiveLabel.getExpr(), state.getVal());
				if (emitExpr.equals(receiveExpr)) {
					final XtaAction action = XtaAction.synced(state.getLocs(), emitExpr, emitEdge, recieveEdge);
					result.add(action);
				}
			}
		}
	}

	private static void addSimpleActionsForEdge(final Collection<XtaAction> result, final XtaState<?> state,
			final Edge edge) {
		final XtaAction action = XtaAction.simple(state.getLocs(), edge);
		result.add(action);
	}

}
