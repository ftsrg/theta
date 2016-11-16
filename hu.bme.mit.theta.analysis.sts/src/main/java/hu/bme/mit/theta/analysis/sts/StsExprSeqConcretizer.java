package hu.bme.mit.theta.analysis.sts;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.ConcretizerOp;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus2;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;

public class StsExprSeqConcretizer implements ConcretizerOp<ExprState, StsAction, ItpRefutation> {

	private final STS sts;
	private final ItpSolver solver;
	private final Expr<? extends BoolType> negProp;

	public StsExprSeqConcretizer(final STS sts, final ItpSolver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
		this.negProp = Exprs.Not(checkNotNull(sts.getProp()));
	}

	@Override
	public ExprTraceStatus2<ItpRefutation> checkConcretizable(final Trace<? extends ExprState, StsAction> cex) {
		checkNotNull(cex);
		checkArgument(cex.length() > 0);

		final List<ItpMarker> markers = new ArrayList<>(cex.length() + 1);
		for (int i = 0; i < cex.length() + 1; ++i) {
			markers.add(solver.createMarker());
		}

		final ItpPattern pattern = solver.createSeqPattern(markers);

		solver.push();
		solver.add(markers.get(0), sts.unfoldInit(0));
		for (int i = 0; i < cex.length(); ++i) {
			solver.add(markers.get(i), sts.unfoldInv(i));
			solver.add(markers.get(i), sts.unfold(cex.getState(i).toExpr(), i));
			if (i > 0) {
				solver.add(markers.get(i), sts.unfoldTrans(i - 1));
			}
		}
		solver.add(markers.get(cex.length()), sts.unfold(negProp, cex.length() - 1));

		final boolean concretizable = solver.check().isSat();

		ExprTraceStatus2<ItpRefutation> status = null;

		if (concretizable) {
			final List<Valuation> trace = sts.extractTrace(solver.getModel(), cex.length());
			status = ExprTraceStatus2.feasible(trace);
		} else {
			final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
			for (int i = 0; i < markers.size() - 1; ++i) {
				interpolants.add(sts.foldin(solver.getInterpolant(pattern).eval(markers.get(i)), i));
			}
			status = ExprTraceStatus2.infeasible(ItpRefutation.sequence(interpolants));
		}

		solver.pop();

		assert status != null;
		return status;
	}

}
