package hu.bme.mit.theta.splittingcegar.common.steps;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractState;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractSystem;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;

/**
 * Base class for concretizing linear counterexamples.
 */
public abstract class AbstractConcretizer extends AbstractCEGARStep {

	public AbstractConcretizer(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	/**
	 * Concretize a general counterexample, which can be described as a list of
	 * expressions. Returns the longest concrete trace that corresponds to a
	 * prefix of the abstract counterexample.
	 */
	protected ConcreteTrace concretize(final AbstractSystem system, final List<? extends AbstractState> counterEx,
			final Expr<? extends BoolType> lastState, final Collection<VarDecl<?>> requiredVars) {
		// Do an iterative bounded model checking to find a concrete
		// counterexample.
		// Iterative method is required because if no counterexample exists, we
		// would like to know which is
		// the first abstract state in the abstract counterexample that has no
		// corresponding concrete state
		// (or if the last state is not bad).
		final STS sts = system.getSTS();
		final Solver solver = solvers.getSolver();

		Model model = null;

		solver.push();
		solver.add(sts.unfoldInit(0)); // Assert initial conditions

		// Loop through each abstract state in the abstract counterexample and
		// assert:
		// - Invariants
		// - Labels of the abstract state
		// - Transition relation from the previous state to the actual state
		// (i>0)
		int len = 0;
		for (int i = 0; i < counterEx.size(); ++i) {
			if (stopHandler.isStopped())
				return null;
			solver.add(sts.unfold(counterEx.get(i).createExpression(), i)); // Labels
			if (i > 0)
				solver.add(sts.unfoldTrans(i - 1)); // Transition relation

			if (SolverHelper.checkSat(solver))
				model = solver.getModel();
			else {
				len = i;
				break;
			}
		}

		if (solver.getStatus() == SolverStatus.SAT)
			len = counterEx.size();

		// If a trace as long as the abstract counterexample was found,
		// check if the last state violates the specification
		if (lastState != null && solver.getStatus() == SolverStatus.SAT) {
			solver.add(sts.unfold(lastState, counterEx.size() - 1));
			if (SolverHelper.checkSat(solver))
				model = solver.getModel();
		}

		// Extract trace (at this point model should not be null,
		// since for i=0 it must be satisfiable)
		assert model != null;

		final List<Valuation> trace = sts.extractTrace(model, len, requiredVars);

		final ConcreteTrace result = new ConcreteTrace(trace, solver.getStatus() == SolverStatus.SAT);
		solver.pop();

		// Print result
		if (result.isCounterexample()) {
			logger.writeln("Concrete counterexample found.", 2, 0);
			for (final Valuation m : result.getTrace())
				logger.writeln(m, 4, 1);
		} else {
			logger.writeln("No concrete counterexample was found, length of trace: " + result.getTrace().size(), 2);
			for (final Valuation m : result.getTrace())
				logger.writeln(m, 4, 1);
		}

		return result;
	}
}
