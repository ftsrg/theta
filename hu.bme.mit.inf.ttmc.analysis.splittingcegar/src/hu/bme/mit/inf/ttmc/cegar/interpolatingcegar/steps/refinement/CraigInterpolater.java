package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.Interpolant;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

public class CraigInterpolater extends AbstractCEGARStep implements Interpolater {

	public CraigInterpolater(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public Interpolant interpolate(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {
		final ItpSolver interpolatingSolver = system.getManager().getSolverFactory().createItpSolver();
		final int traceLength = concreteTrace.getTrace().size();

		final ItpMarker A = interpolatingSolver.createMarker();
		final ItpMarker B = interpolatingSolver.createMarker();
		final ItpPattern pattern = interpolatingSolver.createBinPattern(A, B);

		final STS sts = system.getSTS();

		interpolatingSolver.push();

		// The first formula (A) describes the dead-end states
		interpolatingSolver.add(A, sts.unrollInit(0)); // Start from an initial state
		for (int i = 0; i < traceLength; ++i) {
			for (final Expr<? extends BoolType> label : abstractCounterEx.get(i).getLabels())
				interpolatingSolver.add(A, sts.unroll(label, i)); // Labels of the abstract state
			if (i > 0)
				interpolatingSolver.add(A, sts.unrollTrans(i - 1)); // Transition relation
			interpolatingSolver.add(A, sts.unrollInv(i)); // Invariants
		}

		// The second formula (B) describes the bad states, which are:
		// - States with transitions to the next abstract state (if the failure state is not the last)
		// - States violating the property (if the failure state is the last)
		if (traceLength < abstractCounterEx.size()) { // Failure state is not the last
			for (final Expr<? extends BoolType> label : abstractCounterEx.get(traceLength).getLabels())
				interpolatingSolver.add(B, sts.unroll(label, traceLength)); // Labels of the next abstract state
			interpolatingSolver.add(B, sts.unrollInv(traceLength)); // Invariants for the next abstract state
			interpolatingSolver.add(B, sts.unrollTrans(traceLength - 1)); // Transition to the next abstract state
		} else { // Failure state is the last
			final NotExpr negSpec = system.getManager().getExprFactory().Not(system.getSTS().getProp());
			interpolatingSolver.add(B, sts.unroll(negSpec, traceLength - 1)); // Property violation
		}
		// Since A and B is unsatisfiable (otherwise there would be a concrete counterexample),
		// an invariant I must exist with A -> I, I and B unsat and I contains only variables with
		// the index (traceLength-1), thus splitting the failure state
		interpolatingSolver.check();
		final Expr<? extends BoolType> interpolant = sts.foldin(interpolatingSolver.getInterpolant(pattern).eval(A), traceLength - 1);

		interpolatingSolver.pop();
		return new Interpolant(interpolant, traceLength - 1, system.getManager());
	}

	@Override
	public String toString() {
		return "craigItp";
	}
}
