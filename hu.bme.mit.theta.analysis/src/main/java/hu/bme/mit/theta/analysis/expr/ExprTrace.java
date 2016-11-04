package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.solver.utils.SolverUtils.using;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverStatus;

public final class ExprTrace {
	private final List<Expr<? extends BoolType>> exprs;
	private final List<VarIndexing> indexings;

	private ExprTrace(final List<? extends ExprAction> actions) {
		checkNotNull(actions);

		exprs = new ArrayList<>();
		indexings = new ArrayList<>();

		VarIndexing currentIndexing = VarIndexing.all(0);
		indexings.add(currentIndexing);
		for (final ExprAction action : actions) {
			exprs.add(PathUtils.unfold(action.toExpr(), currentIndexing));
			currentIndexing = currentIndexing.add(action.nextIndexing());
			indexings.add(currentIndexing);
		}
	}

	public static ExprTrace of(final List<? extends ExprAction> actions) {
		return new ExprTrace(actions);
	}

	public ExprTraceStatus check(final ItpSolver solver) {
		return using(solver, s -> {
			final List<ItpMarker> markers = new ArrayList<>();

			markers.add(s.createMarker());
			for (final Expr<? extends BoolType> expr : exprs) {
				final ItpMarker marker = s.createMarker();
				markers.add(marker);
				s.add(marker, expr);
			}

			final ItpPattern pattern = s.createSeqPattern(markers);

			final SolverStatus status = s.check();
			final ExprTraceStatus result;

			if (status.isSat()) {
				final Model model = s.getModel();
				result = ExprTraceStatus.feasable(model, indexings);
			} else {
				final Interpolant interpolant = s.getInterpolant(pattern);
				result = ExprTraceStatus.unfeasable(interpolant, markers, indexings);
			}

			return result;
		});
	}

	////

}
