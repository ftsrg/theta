package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.Interpolant;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.solver.ItpSolver;

/**
 * Calculate sequence interpolant.
 *
 * @author Akos
 */
public class SequenceInterpolater extends AbstractCEGARStep implements Interpolater {

	/**
	 * Initialize the interpolater with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 * @param interpolatingSolver
	 */
	public SequenceInterpolater(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public Interpolant interpolate(final InterpolatedAbstractSystem system,
			final List<InterpolatedAbstractState> abstractCounterEx, final ConcreteTrace concreteTrace) {

		final ItpSolver interpolatingSolver = system.getManager().getSolverFactory().createItpSolver();
		// Create pattern for a sequence interpolant
		final ItpMarker[] markers = new ItpMarker[abstractCounterEx.size() + 1];
		for (int i = 0; i < markers.length; ++i)
			markers[i] = interpolatingSolver.createMarker();

		final ItpPattern pattern = interpolatingSolver.createSeqPattern(Arrays.asList(markers));

		// Create an sts for the size of the abstract trace
		final STS sts = system.getSTS();

		interpolatingSolver.push();

		// Initial conditions for the first marker
		interpolatingSolver.add(markers[0], sts.unrollInit(0));

		// Loop through each marker except the last one
		for (int i = 0; i < abstractCounterEx.size(); ++i) {

			for (final Expr<? extends BoolType> label : abstractCounterEx.get(i).getLabels()) {
				// Assert labels
				interpolatingSolver.add(markers[i], sts.unroll(label, i));
			}

			if (i > 0) {
				// Assert transition relation
				interpolatingSolver.add(markers[i], sts.unrollTrans(i - 1));
			}

			// Assert invariants
			interpolatingSolver.add(markers[i], sts.unrollInv(i));

		}

		// Set the last marker
		final NotExpr negSpec = system.getManager().getExprFactory().Not(system.getSTS().getProp());
		interpolatingSolver.add(markers[abstractCounterEx.size()], sts.unroll(negSpec, abstractCounterEx.size() - 1)); // Property
																														// violation

		// The conjunction of the markers is unsatisfiable (otherwise there
		// would be a concrete counterexample),
		// thus an interpolant sequence must exist. The first one is always
		// 'true' and it is not returned by the
		// solver, but the last one is always 'false' and it is returned
		interpolatingSolver.check();
		final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
		// Fold in interpolants (except the last)
		for (int i = 0; i < markers.length - 1; ++i)
			interpolants.add(sts.foldin(interpolatingSolver.getInterpolant(pattern).eval(markers[i]), i));

		// TODO: assert last interpolant to be 'false'

		interpolatingSolver.pop();

		return new Interpolant(interpolants);
	}

	@Override
	public String toString() {
		return "seqItp";
	}
}
