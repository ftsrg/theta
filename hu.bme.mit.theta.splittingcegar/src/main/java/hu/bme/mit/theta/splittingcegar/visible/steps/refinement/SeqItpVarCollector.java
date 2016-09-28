package hu.bme.mit.theta.splittingcegar.visible.steps.refinement;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
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
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractState;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractSystem;

public class SeqItpVarCollector extends AbstractCEGARStep implements VarCollector {

	public SeqItpVarCollector(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public Collection<VarDecl<? extends Type>> collectVars(final VisibleAbstractSystem system,
			final List<VisibleAbstractState> abstractCounterEx, final ConcreteTrace concreteCounterEx) {

		final ItpSolver itpSolver = solvers.getItpSolver();

		final ItpMarker[] markers = new ItpMarker[abstractCounterEx.size()];
		for (int i = 0; i < markers.length; ++i)
			markers[i] = itpSolver.createMarker();

		final ItpPattern pattern = itpSolver.createSeqPattern(Arrays.asList(markers));

		final STS sts = system.getSTS();

		itpSolver.push();

		// Initial conditions for the first marker
		itpSolver.add(markers[0], sts.unfoldInit(0));
		// Loop through each marker
		for (int i = 0; i < abstractCounterEx.size(); ++i) {
			// Assert labels
			itpSolver.add(markers[i], sts.unfold(abstractCounterEx.get(i).getValuation().toExpr(), i));

			if (i > 0) {
				// Assert transition relation
				itpSolver.add(markers[i], sts.unfoldTrans(i - 1));
			}

			// Assert invariants
			itpSolver.add(markers[i], sts.unfoldInv(i));

		}

		// The conjunction of the markers is unsatisfiable (otherwise there
		// would be a concrete counterexample),
		// thus an interpolant sequence must exist. The first one is always
		// 'true' and it is not returned by the
		// solver, but the last one is always 'false' and it is returned
		itpSolver.check();
		assert (itpSolver.getStatus() == SolverStatus.UNSAT);
		final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
		// Fold in interpolants (except the last)
		for (int i = 0; i < markers.length - 1; ++i)
			interpolants.add(sts.foldin(itpSolver.getInterpolant(pattern).eval(markers[i]), i));

		itpSolver.pop();

		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		for (final Expr<? extends BoolType> interpolant : interpolants)
			ExprUtils.collectVars(interpolant, vars);

		return vars;
	}

	@Override
	public String toString() {
		return "seqItpVarColl";
	}
}
