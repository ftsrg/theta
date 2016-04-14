package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.ttmc.cegar.common.data.StopHandler;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.Interpolant;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.solver.SolverStatus;

public class CraigInterpolater extends AbstractCEGARStep implements Interpolater {

	public CraigInterpolater(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public Interpolant interpolate(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {
		final int traceLength = concreteTrace.getTrace().size();

		final ItpSolver itpSolver = solvers.getItpSolver();

		final ItpMarker A = itpSolver.createMarker();
		final ItpMarker B = itpSolver.createMarker();
		final ItpPattern pattern = itpSolver.createBinPattern(A, B);

		final STS sts = system.getSTS();

		itpSolver.push();

		// The first formula (A) describes the dead-end states

		// Start from an initial state
		itpSolver.add(A, sts.unrollInit(0));

		for (int i = 0; i < traceLength; ++i) {
			for (final Expr<? extends BoolType> label : abstractCounterEx.get(i).getLabels()) {
				// Labels of the abstract state
				itpSolver.add(A, sts.unroll(label, i));
			}

			if (i > 0) {
				// Transition relation
				itpSolver.add(A, sts.unrollTrans(i - 1));
			}

			// Invariants
			itpSolver.add(A, sts.unrollInv(i));

		}

		// The second formula (B) describes the bad states, which are:
		// - States with transitions to the next abstract state (if the failure
		// state is not the last)
		// - States violating the property (if the failure state is the last)
		if (traceLength < abstractCounterEx.size()) { // Failure state is not
															// the last
			for (final Expr<? extends BoolType> label : abstractCounterEx.get(traceLength).getLabels())
				// Labels of the next abstract state
				itpSolver.add(B, sts.unroll(label, traceLength));
			// Invariants for the next abstract state
			itpSolver.add(B, sts.unrollInv(traceLength));
			// Transition to the next abstract state
			itpSolver.add(B, sts.unrollTrans(traceLength - 1));

		} else { // Failure state is the last
			final NotExpr negSpec = Exprs.Not(system.getSTS().getProp());
			// Property violation
			itpSolver.add(B, sts.unroll(negSpec, traceLength - 1));

		}
		// Since A and B is unsatisfiable (otherwise there would be a concrete
		// counterexample),
		// an invariant I must exist with A -> I, I and B unsat and I contains
		// only variables with
		// the index (traceLength-1), thus splitting the failure state
		itpSolver.check();
		assert (itpSolver.getStatus() == SolverStatus.UNSAT);
		final hu.bme.mit.inf.ttmc.solver.Interpolant itp = itpSolver.getInterpolant(pattern);

		try {
			final Expr<? extends BoolType> interpolant = sts.foldin(itp.eval(A), traceLength - 1);
			itpSolver.pop();
			return new Interpolant(interpolant, traceLength - 1);
		} catch (final Exception ex) {
			itpSolver.getInterpolant(pattern);
			throw new AssertionError();
		}

	}

	@Override
	public String toString() {
		return "craigItp";
	}
}
