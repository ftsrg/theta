package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.constraint.solver.SolverStatus;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class SeqItpVarCollector extends AbstractCEGARStep implements VarCollector {

	public SeqItpVarCollector(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public Collection<VarDecl<? extends Type>> collectVars(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx,
			final ConcreteTrace concreteCounterEx) {
		final ItpSolver itpSolver = system.getManager().getSolverFactory().createItpSolver();

		final ItpMarker[] markers = new ItpMarker[abstractCounterEx.size()];
		for (int i = 0; i < markers.length; ++i)
			markers[i] = itpSolver.createMarker();

		final ItpPattern pattern = itpSolver.createSeqPattern(Arrays.asList(markers));

		final STSUnroller unroller = system.getUnroller();

		itpSolver.push();

		itpSolver.add(markers[0], unroller.init(0)); // Initial conditions for the first marker
		for (int i = 0; i < abstractCounterEx.size(); ++i) { // Loop through each marker
			itpSolver.add(markers[i], unroller.unroll(abstractCounterEx.get(i).getExpression(), i)); // Assert labels
			if (i > 0)
				itpSolver.add(markers[i], unroller.trans(i - 1)); // Assert transition relation
			itpSolver.add(markers[i], unroller.inv(i)); // Assert invariants
		}

		// The conjunction of the markers is unsatisfiable (otherwise there would be a concrete counterexample),
		// thus an interpolant sequence must exist. The first one is always 'true' and it is not returned by the
		// solver, but the last one is always 'false' and it is returned
		itpSolver.check();
		assert (itpSolver.getStatus() == SolverStatus.UNSAT);
		final List<Expr<? extends BoolType>> interpolants = new ArrayList<>();
		// Fold in interpolants (except the last)
		for (int i = 0; i < markers.length - 1; ++i)
			interpolants.add(unroller.foldin(itpSolver.getInterpolant(pattern).eval(markers[i]), i));

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
