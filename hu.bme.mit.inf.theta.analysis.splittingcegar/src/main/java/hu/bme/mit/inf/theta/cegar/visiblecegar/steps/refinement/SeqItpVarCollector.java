package hu.bme.mit.inf.theta.cegar.visiblecegar.steps.refinement;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.inf.theta.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.theta.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.theta.cegar.common.data.StopHandler;
import hu.bme.mit.inf.theta.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.theta.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.theta.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.theta.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.theta.common.logging.Logger;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.formalism.utils.FormalismUtils;
import hu.bme.mit.inf.theta.solver.ItpMarker;
import hu.bme.mit.inf.theta.solver.ItpPattern;
import hu.bme.mit.inf.theta.solver.ItpSolver;
import hu.bme.mit.inf.theta.solver.SolverStatus;

public class SeqItpVarCollector extends AbstractCEGARStep implements VarCollector {

	public SeqItpVarCollector(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public Collection<VarDecl<? extends Type>> collectVars(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx,
			final ConcreteTrace concreteCounterEx) {

		final ItpSolver itpSolver = solvers.getItpSolver();

		final ItpMarker[] markers = new ItpMarker[abstractCounterEx.size()];
		for (int i = 0; i < markers.length; ++i)
			markers[i] = itpSolver.createMarker();

		final ItpPattern pattern = itpSolver.createSeqPattern(Arrays.asList(markers));

		final STS sts = system.getSTS();

		itpSolver.push();

		// Initial conditions for the first marker
		itpSolver.add(markers[0], sts.unrollInit(0));
		// Loop through each marker
		for (int i = 0; i < abstractCounterEx.size(); ++i) {
			// Assert labels
			itpSolver.add(markers[i], sts.unroll(abstractCounterEx.get(i).getValuation().toExpr(), i));

			if (i > 0) {
				// Assert transition relation
				itpSolver.add(markers[i], sts.unrollTrans(i - 1));
			}

			// Assert invariants
			itpSolver.add(markers[i], sts.unrollInv(i));

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
			FormalismUtils.collectVars(interpolant, vars);

		return vars;
	}

	@Override
	public String toString() {
		return "seqItpVarColl";
	}
}
