package hu.bme.mit.inf.ttmc.cegar.common.steps;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Model;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.solver.SolverStatus;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * Base class for concretizing linear counterexamples.
 *
 * @author Akos
 */
public abstract class ConcretizerBase extends CEGARStepBase {

	/**
	 * Initialize the step with a manager, logger and visualizer
	 *
	 * @param manager
	 * @param logger
	 * @param visualizer
	 */
	public ConcretizerBase(final Logger logger, final IVisualizer visualizer) {
		super(logger, visualizer);
	}

	/**
	 * Concretize a general counterexample, which can be described as a list of
	 * expressions. Returns the longest concrete trace that corresponds to a
	 * prefix of the abstract counterexample.
	 *
	 * @param unroller
	 *            Unroller for the concrete system
	 * @param counterEx
	 *            Counterexample represented as a list of expressions
	 * @param lastState
	 *            Expression that must hold for the last state (it can be null)
	 * @param removeVariables
	 *            Collection of variables that have to be removed from the model
	 *            (it can be null)
	 * @return Longest concrete trace corresponding to a prefix of the abstract
	 *         counterexample
	 */
	protected ConcreteTrace concretize(final STSManager manager, final STSUnroller unroller, final List<? extends IAbstractState> counterEx,
			final Expr<? extends BoolType> lastState, final Collection<VarDecl<?>> projectVars) {
		// Do an iterative bounded model checking to find a concrete
		// counterexample.
		// Iterative method is required because if no counterexample exists, we
		// would
		// like to know which is the first abstract state in the abstract
		// counterexample
		// that has no corresponding concrete state (or if the last state is not
		// bad).
		final Solver solver = manager.getSolverFactory().createSolver(true, false);
		Model model = null;

		solver.push();
		solver.add(unroller.init(0)); // Assert initial conditions

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
			solver.add(unroller.inv(i)); // Invariants
			solver.add(unroller.unroll(counterEx.get(i).createExpression(manager), i)); // Labels
			if (i > 0)
				solver.add(unroller.trans(i - 1)); // Transition relation

			if (SolverHelper.checkSatisfiable(solver))
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
			solver.add(unroller.unroll(lastState, counterEx.size() - 1));
			if (SolverHelper.checkSatisfiable(solver))
				model = solver.getModel();
		}

		// Extract trace (at this point model should not be null,
		// since for i=0 it must be satisfiable)
		assert model != null;

		final List<AndExpr> trace = unroller.extractTrace(model, len, projectVars);

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
