package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.KripkeStructure;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.Interpolant;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * State splitter that cuts only states that are in the abstract counterexample.
 * Using a binary interpolant, only the failure state is split, but using a
 * sequence interpolant, multiple states can be split.
 *
 * @author Akos
 */
public class CounterexampleSplitter extends CEGARStepBase implements IStateSplitter {

	/**
	 * Initialize the splitter with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 */
	public CounterexampleSplitter(final STSManager manager, final Logger logger, final IVisualizer visualizer) {
		super(manager, logger, visualizer);
	}

	@Override
	public int split(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx, final Interpolant interpolant) {
		assert (0 < interpolant.size() && interpolant.size() <= abstractCounterEx.size());
		int firstSplit = -1;
		for (int i = 0; i < interpolant.size(); ++i) {
			if (isStopped)
				return 0;
			if (!interpolant.get(i).equals(manager.getExprFactory().True())) {
				split(system, abstractCounterEx.get(i), interpolant.get(i));
				if (firstSplit == -1)
					firstSplit = i;
			}
		}
		assert (0 <= firstSplit && firstSplit < abstractCounterEx.size());
		return firstSplit;
	}

	private void split(final InterpolatedAbstractSystem system, final InterpolatedAbstractState failureState, Expr<? extends BoolType> interpolant) {
		// Create unroller for k=1
		final STSUnroller unroller = system.getUnroller();

		// Refine the abstract Kripke structure
		final KripkeStructure<InterpolatedAbstractState> ks = system.getAbstractKripkeStructure();

		// Remove negations from the interpolant (to avoid multiple negations)
		while (interpolant instanceof NotExpr)
			interpolant = ((NotExpr) interpolant).getOp();

		logger.writeln("Refining " + failureState, 5, 1);

		// Create refined abstract states using the interpolant and its negation
		final List<InterpolatedAbstractState> refinedStates = new ArrayList<>(2);
		refinedStates.add(failureState.refine(interpolant));
		refinedStates.add(failureState.refine(manager.getExprFactory().Not(interpolant)));
		// Check for contradicting labels
		for (final InterpolatedAbstractState refined : refinedStates) {
			solver.push();
			SolverHelper.unrollAndAssert(solver, refined.getLabels(), unroller, 0);
			final boolean check = SolverHelper.checkSatisfiable(solver);
			solver.pop();
			if (!check) {
				logger.writeln("Cannot refine.", 5, 2);
				return;
			}
		}

		// Remove the original state
		ks.getStates().remove(failureState);
		ks.getInitialStates().remove(failureState);

		logger.writeln(refinedStates.size() + " new abstract states.", 5, 1);
		for (final InterpolatedAbstractState refined : refinedStates)
			logger.writeln(refined, 6, 2);

		// Check if the refined states are initial (only if the original state was initial, but
		// then at least one of the refined states must also be initial --> assertion)
		if (failureState.isInitial()) {
			solver.push();
			solver.add(unroller.inv(0));
			solver.add(unroller.init(0));
			boolean isInitial = false;
			for (final InterpolatedAbstractState refined : refinedStates) {
				solver.push();
				SolverHelper.unrollAndAssert(solver, refined.getLabels(), unroller, 0);
				refined.setInitial(SolverHelper.checkSatisfiable(solver));
				if (refined.isInitial())
					isInitial = true;
				solver.pop();
			}
			assert (isInitial);
			solver.pop();
		}

		if (isStopped)
			return;

		// Get successors for the abstract states (only the successors of the original state
		// have to be checked, but every successor must belong to at least one of the
		// refined states --> assertion)
		solver.push();
		solver.add(unroller.inv(0));
		solver.add(unroller.inv(1));
		solver.add(unroller.trans(0));
		for (final InterpolatedAbstractState succ : failureState.getSuccessors()) {
			if (isStopped)
				return;
			if (succ.equals(failureState))
				continue;
			// The failure state has to be removed from predecessors
			final boolean removed = succ.getPredecessors().remove(failureState);
			assert (removed);
			solver.push();
			SolverHelper.unrollAndAssert(solver, succ.getLabels(), unroller, 1);
			boolean isSuccessor = false;
			for (final InterpolatedAbstractState refined : refinedStates) {
				if (isStopped)
					return;
				solver.push();
				SolverHelper.unrollAndAssert(solver, refined.getLabels(), unroller, 0);
				if (SolverHelper.checkSatisfiable(solver)) {
					refined.addSuccessor(succ);
					succ.addPredecessor(refined);
					isSuccessor = true;
				}
				solver.pop();
			}
			assert (isSuccessor);
			solver.pop();
		}

		// Get predecessors for the abstract states (only the predecessors of the original state
		// have to be checked, but every predecessor must belong to at least one of the
		// refined states --> assertion)
		for (final InterpolatedAbstractState prev : failureState.getPredecessors()) {
			if (isStopped)
				return;
			if (prev.equals(failureState))
				continue;
			final boolean removed = prev.getSuccessors().remove(failureState);
			assert (removed);
			solver.push();
			SolverHelper.unrollAndAssert(solver, prev.getLabels(), unroller, 0);
			boolean isPredecessor = false;
			for (final InterpolatedAbstractState refined : refinedStates) {
				if (isStopped)
					return;
				solver.push();
				SolverHelper.unrollAndAssert(solver, refined.getLabels(), unroller, 1);
				if (SolverHelper.checkSatisfiable(solver)) {
					prev.addSuccessor(refined);
					refined.addPredecessor(prev);
					isPredecessor = true;
				}
				solver.pop();
			}
			solver.pop();
			assert (isPredecessor);
		}

		// Check transitions between refined states (only if the failure state was a successor
		// of itself, but then at least one transition must also be present between the
		// refined states --> assertion)
		if (failureState.getSuccessors().contains(failureState)) {
			boolean isSuccessor = false;
			for (final InterpolatedAbstractState ref0 : refinedStates) {
				if (isStopped)
					return;
				solver.push();
				SolverHelper.unrollAndAssert(solver, ref0.getLabels(), unroller, 0);
				for (final InterpolatedAbstractState ref1 : refinedStates) {
					if (isStopped)
						return;
					solver.push();
					SolverHelper.unrollAndAssert(solver, ref1.getLabels(), unroller, 1);
					if (SolverHelper.checkSatisfiable(solver)) {
						ref0.addSuccessor(ref1);
						ref1.addPredecessor(ref0);
						isSuccessor = true;
					}
					solver.pop();
				}
				solver.pop();
			}
			assert (isSuccessor);
		}

		solver.pop();

		// Add new states
		ks.getStates().addAll(refinedStates);
		for (final InterpolatedAbstractState refined : refinedStates)
			if (refined.isInitial())
				ks.addInitialState(refined);
	}
}
