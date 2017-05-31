package hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.interpolating.data.Interpolant;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractState;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractSystem;

/**
 * Calculate a sequence interpolant.
 *
 * @author Akos Hajdu
 */
public class SequenceInterpolater extends AbstractCEGARStep implements Interpolater {

	public SequenceInterpolater(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public Interpolant interpolate(final InterpolatedAbstractSystem system,
			final List<InterpolatedAbstractState> abstractCounterEx, final ConcreteTrace concreteTrace) {

		final ItpSolver itpSolver = solvers.getItpSolver();

		// Create pattern for a sequence interpolant
		final ItpMarker[] markers = new ItpMarker[abstractCounterEx.size() + 1];
		for (int i = 0; i < markers.length; ++i)
			markers[i] = itpSolver.createMarker();

		final ItpPattern pattern = itpSolver.createSeqPattern(Arrays.asList(markers));

		// Create an sts for the size of the abstract trace
		final STS sts = system.getSTS();

		itpSolver.push();

		// Initial conditions for the first marker
		itpSolver.add(markers[0], PathUtils.unfold(sts.getInit(), 0));

		// Loop through each marker except the last one
		for (int i = 0; i < abstractCounterEx.size(); ++i) {

			for (final Expr<? extends BoolType> label : abstractCounterEx.get(i).getLabels()) {
				// Assert labels
				itpSolver.add(markers[i], PathUtils.unfold(label, i));
			}

			if (i > 0) {
				// Assert transition relation
				itpSolver.add(markers[i], PathUtils.unfold(sts.getTrans(), i - 1));
			}
		}

		// Set the last marker
		final NotExpr negSpec = Not(system.getSTS().getProp());
		itpSolver.add(markers[abstractCounterEx.size()], PathUtils.unfold(negSpec, abstractCounterEx.size() - 1)); // Property
																													// violation

		// The conjunction of the markers is unsatisfiable (otherwise there
		// would be a concrete counterexample),
		// thus an interpolant sequence must exist. The first one is always
		// 'true' and it is not returned by the
		// solver, but the last one is always 'false' and it is returned
		itpSolver.check();
		final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
		// Fold in interpolants (except the last)
		for (int i = 0; i < markers.length - 1; ++i)
			interpolants.add(PathUtils.foldin(itpSolver.getInterpolant(pattern).eval(markers[i]), i));

		// TODO: assert last interpolant to be 'false'

		itpSolver.pop();

		return new Interpolant(interpolants);
	}

	@Override
	public String toString() {
		return "seqItp";
	}
}
