package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class CraigItpVarCollector extends CEGARStepBase implements IVarCollector {

	/**
	 * Initialize the step with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 * @param interpolatingSolver
	 */
	public CraigItpVarCollector(final Logger logger, final IVisualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public Collection<VarDecl<? extends Type>> collectVariables(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {
		final ItpSolver interpolatingSolver = system.getManager().getSolverFactory().createItpSolver();
		final int traceLength = concreteTrace.size();
		assert (traceLength < abstractCounterEx.size());
		// Create pattern for a binary interpolant
		final ItpMarker A = interpolatingSolver.createMarker();
		final ItpMarker B = interpolatingSolver.createMarker();
		final ItpPattern pattern = interpolatingSolver.createBinPattern(A, B);
		// Create an unroller for the size of the trace
		final STSUnroller unroller = system.getUnroller();

		interpolatingSolver.push();
		// The first formula (A) describes the dead-end states
		interpolatingSolver.add(A, unroller.init(0));
		for (int i = 0; i < traceLength; ++i) {
			interpolatingSolver.add(A, unroller.unroll(abstractCounterEx.get(i).getExpression(), i)); // Expression of the abstract state
			if (i > 0)
				interpolatingSolver.add(A, unroller.trans(i - 1)); // Transition relation
			interpolatingSolver.add(A, unroller.inv(i)); // Invariants
		}
		// The second formula (B) describes the bad states, which are states with
		// transitions to the next abstract state
		interpolatingSolver.add(B, unroller.unroll(abstractCounterEx.get(traceLength).getExpression(), traceLength)); // Expression of the next abstract state
		interpolatingSolver.add(B, unroller.inv(traceLength)); // Invariants for the next abstract state
		interpolatingSolver.add(B, unroller.trans(traceLength - 1)); // Transition to the next abstract state

		// Since A and B is unsatisfiable (otherwise there would be a concrete counterexample),
		// an invariant I must exist with A -> I, I and B unsat and I contains only variables with
		// the index (traceLength-1), thus splitting the failure state
		interpolatingSolver.check();
		final Expr<? extends Type> interpolant = unroller.foldin(interpolatingSolver.getInterpolant(pattern).eval(A), traceLength - 1);
		logger.writeln("Interpolant: " + interpolant, 4, 0);
		interpolatingSolver.pop();
		return FormalismUtils.collectVars(interpolant);
	}

	@Override
	public String toString() {
		return "craigItpVarColl";
	}
}
