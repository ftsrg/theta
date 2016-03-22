package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
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
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * Calculate sequence interpolant.
 *
 * @author Akos
 */
public class SequenceInterpolater extends CEGARStepBase implements IInterpolater {
	private final ItpSolver interpolatingSolver;

	/**
	 * Initialize the interpolater with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 * @param interpolatingSolver
	 */
	public SequenceInterpolater(final STSManager manager, final Logger logger, final IVisualizer visualizer) {
		super(manager, logger, visualizer);
		this.interpolatingSolver = manager.getSolverFactory().createItpSolver();
	}

	@Override
	public Interpolant interpolate(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {

		// Create pattern for a sequence interpolant
		final ItpMarker[] markers = new ItpMarker[abstractCounterEx.size() + 1];
		for (int i = 0; i < markers.length; ++i)
			markers[i] = interpolatingSolver.createMarker();

		final ItpPattern pattern = interpolatingSolver.createSeqPattern(Arrays.asList(markers));

		// Create an unroller for the size of the abstract trace
		final STSUnroller unroller = system.getUnroller();

		interpolatingSolver.push();

		interpolatingSolver.add(markers[0], unroller.init(0)); // Initial conditions for the first marker
		for (int i = 0; i < abstractCounterEx.size(); ++i) { // Loop through each marker except the last one
			for (final Expr<? extends BoolType> label : abstractCounterEx.get(i).getLabels())
				interpolatingSolver.add(markers[i], unroller.unroll(label, i)); // Assert labels
			if (i > 0)
				interpolatingSolver.add(markers[i], unroller.trans(i - 1)); // Assert transition relation
			interpolatingSolver.add(markers[i], unroller.inv(i)); // Assert invariants
		}

		// Set the last marker
		final NotExpr negSpec = manager.getExprFactory().Not(system.getSystem().getProp());
		interpolatingSolver.add(markers[abstractCounterEx.size()], unroller.unroll(negSpec, abstractCounterEx.size() - 1)); // Property violation

		// The conjunction of the markers is unsatisfiable (otherwise there would be a concrete counterexample),
		// thus an interpolant sequence must exist. The first one is always 'true' and it is not returned by the
		// solver, but the last one is always 'false' and it is returned
		interpolatingSolver.check();
		final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
		// Fold in interpolants (except the last)
		for (int i = 0; i < markers.length - 1; ++i)
			interpolants.add(unroller.foldin(interpolatingSolver.getInterpolant(pattern).eval(markers[i]), i));

		// TODO: assert last interpolant to be 'false'

		interpolatingSolver.pop();

		return new Interpolant(interpolants);
	}

	@Override
	public String toString() {
		return "seqInterpol";
	}
}
