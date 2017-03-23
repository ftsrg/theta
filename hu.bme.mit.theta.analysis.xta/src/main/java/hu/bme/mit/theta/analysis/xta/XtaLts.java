package hu.bme.mit.theta.analysis.xta;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.xta.SyncLabel;
import hu.bme.mit.theta.formalism.xta.SyncLabel.Kind;
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

		final List<Loc> locs = state.getLocs();
		for (final Loc loc : locs) {
			final Collection<Edge> edges = loc.getOutEdges();
			for (final Edge edge : edges) {
				if (edge.getSync().isPresent()) {
					final SyncLabel label = edge.getSync().get();
					final Kind kind = label.getKind();
					if (kind == Kind.EMIT) {
						final Expr<?> expr = ExprUtils.simplify(label.getExpr(), state.getVal());
						for (final Loc otherLoc : locs) {
							if (otherLoc != loc) {
								for (final Edge otherEdge : otherLoc.getOutEdges()) {
									if (otherEdge.getSync().isPresent()) {
										final SyncLabel otherLabel = otherEdge.getSync().get();
										final Kind otherKind = otherLabel.getKind();
										if (otherKind == Kind.RECEIVE) {
											final Expr<?> otherExpr = ExprUtils.simplify(otherLabel.getExpr(),
													state.getVal());
											if (expr.equals(otherExpr)) {
												final XtaAction action = XtaAction.synced(locs, edge, otherEdge);
												result.add(action);
											}
										}
									}
								}
							}
						}
					}
				} else {
					final XtaAction action = XtaAction.simple(locs, edge);
					result.add(action);
				}
			}
		}

		return result;
	}

}
