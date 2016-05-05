package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.ttmc.cegar.common.data.StopHandler;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.solver.ItpSolver;

public class CraigItpVarCollector extends AbstractCEGARStep implements VarCollector {

	public CraigItpVarCollector(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public Collection<VarDecl<? extends Type>> collectVars(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {
		final int traceLength = concreteTrace.size();
		assert (traceLength < abstractCounterEx.size());
		final ItpSolver itpSolver = solvers.getItpSolver();

		final ItpMarker A = itpSolver.createMarker();
		final ItpMarker B = itpSolver.createMarker();
		final ItpPattern pattern = itpSolver.createBinPattern(A, B);

		final STS sts = system.getSTS();

		itpSolver.push();
		// The first formula (A) describes the dead-end states
		itpSolver.add(A, sts.unrollInit(0));
		for (int i = 0; i < traceLength; ++i) {
			// Expression of the abstract state
			itpSolver.add(A, sts.unroll(abstractCounterEx.get(i).getExpression().toExpr(), i));

			if (i > 0) {
				// Transition relation
				itpSolver.add(A, sts.unrollTrans(i - 1));
			}

			// Invariants
			itpSolver.add(A, sts.unrollInv(i));

		}
		// The second formula (B) describes the bad states, which are states
		// with
		// transitions to the next abstract state

		// Expression of the next abstract state
		itpSolver.add(B, sts.unroll(abstractCounterEx.get(traceLength).getExpression().toExpr(), traceLength));
		// Invariants for the next abstract state
		itpSolver.add(B, sts.unrollInv(traceLength));
		// Transition to the next abstract state
		itpSolver.add(B, sts.unrollTrans(traceLength - 1));

		// Since A and B is unsatisfiable (otherwise there would be a concrete
		// counterexample),
		// an invariant I must exist with A -> I, I and B unsat and I contains
		// only variables with
		// the index (traceLength-1), thus splitting the failure state
		itpSolver.check();
		final Expr<? extends Type> interpolant = sts.foldin(itpSolver.getInterpolant(pattern).eval(A), traceLength - 1);

		logger.writeln("Interpolant: " + interpolant, 4, 0);
		itpSolver.pop();
		return FormalismUtils.collectVars(interpolant);
	}

	@Override
	public String toString() {
		return "craigItpVarColl";
	}
}
