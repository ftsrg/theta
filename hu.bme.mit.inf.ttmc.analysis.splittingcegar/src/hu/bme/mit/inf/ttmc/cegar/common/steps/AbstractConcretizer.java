package hu.bme.mit.inf.ttmc.cegar.common.steps;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Model;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverStatus;

/**
 * Base class for concretizing linear counterexamples.
 */
public abstract class AbstractConcretizer extends AbstractCEGARStep {

	public AbstractConcretizer(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
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
		final Solver solver = system.getManager().getSolverFactory().createSolver(true, false);
		Model model = null;

		solver.push();
		solver.add(sts.unrollInit(0)); // Assert initial conditions

		// Loop through each abstract state in the abstract counterexample and
		// assert:
		// - Invariants
		// - Labels of the abstract state
		// - Transition relation from the previous state to the actual state
		// (i>0)
		int len = 0;
		for (int i = 0; i < counterEx.size(); ++i) {
			if (isStopped)
				return null;
			solver.add(sts.unrollInv(i)); // Invariants
			solver.add(sts.unroll(counterEx.get(i).createExpression(system.getManager()), i)); // Labels
			if (i > 0)
				solver.add(sts.unrollTrans(i - 1)); // Transition relation

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
			solver.add(sts.unroll(lastState, counterEx.size() - 1));
			if (SolverHelper.checkSat(solver))
				model = solver.getModel();
		}

		// Extract trace (at this point model should not be null,
		// since for i=0 it must be satisfiable)
		assert model != null;

		final List<AndExpr> trace = sts.extractTrace(model, len, requiredVars);

		final ConcreteTrace result = new ConcreteTrace(trace, solver.getStatus() == SolverStatus.SAT);
		solver.pop();

		// Print result
		if (result.isCounterexample()) {
			logger.writeln("Concrete counterexample found.", 2, 0);
			for (final AndExpr m : result.getTrace())
				logger.writeln(m, 4, 1);
		} else {
			logger.writeln("No concrete counterexample was found, length of trace: " + result.getTrace().size(), 2);
			for (final AndExpr m : result.getTrace())
				logger.writeln(m, 4, 1);
		}

		return result;
	}
}
