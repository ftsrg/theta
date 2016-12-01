package hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement;

import java.util.List;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.NotExpr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.interpolating.data.Interpolant;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractState;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractSystem;

public class CraigInterpolater extends AbstractCEGARStep implements Interpolater {

	public CraigInterpolater(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public Interpolant interpolate(final InterpolatedAbstractSystem system,
			final List<InterpolatedAbstractState> abstractCounterEx, final ConcreteTrace concreteTrace) {
		final int traceLength = concreteTrace.getTrace().size();

		final ItpSolver itpSolver = solvers.getItpSolver();

		final ItpMarker A = itpSolver.createMarker();
		final ItpMarker B = itpSolver.createMarker();
		final ItpPattern pattern = itpSolver.createBinPattern(A, B);

		final STS sts = system.getSTS();

		itpSolver.push();

		// The first formula (A) describes the dead-end states

		// Start from an initial state
		itpSolver.add(A, sts.unfoldInit(0));

		for (int i = 0; i < traceLength; ++i) {
			for (final Expr<? extends BoolType> label : abstractCounterEx.get(i).getLabels()) {
				// Labels of the abstract state
				itpSolver.add(A, sts.unfold(label, i));
			}

			if (i > 0) {
				// Transition relation
				itpSolver.add(A, sts.unfoldTrans(i - 1));
			}

		}

		// The second formula (B) describes the bad states, which are:
		// - States with transitions to the next abstract state (if the failure
		// state is not the last)
		// - States violating the property (if the failure state is the last)
		if (traceLength < abstractCounterEx.size()) { // Failure state is not
														// the last
			for (final Expr<? extends BoolType> label : abstractCounterEx.get(traceLength).getLabels())
				// Labels of the next abstract state
				itpSolver.add(B, sts.unfold(label, traceLength));
			// Transition to the next abstract state
			itpSolver.add(B, sts.unfoldTrans(traceLength - 1));

		} else { // Failure state is the last
			final NotExpr negSpec = Exprs.Not(system.getSTS().getProp());
			// Property violation
			itpSolver.add(B, sts.unfold(negSpec, traceLength - 1));

		}
		// Since A and B is unsatisfiable (otherwise there would be a concrete
		// counterexample),
		// an invariant I must exist with A -> I, I and B unsat and I contains
		// only variables with
		// the index (traceLength-1), thus splitting the failure state
		itpSolver.check();
		assert (itpSolver.getStatus() == SolverStatus.UNSAT);
		final hu.bme.mit.theta.solver.Interpolant itp = itpSolver.getInterpolant(pattern);

		final Expr<? extends BoolType> interpolant = sts.foldin(itp.eval(A), traceLength - 1);
		itpSolver.pop();
		return new Interpolant(interpolant, traceLength - 1);

	}

	@Override
	public String toString() {
		return "craigItp";
	}
}
