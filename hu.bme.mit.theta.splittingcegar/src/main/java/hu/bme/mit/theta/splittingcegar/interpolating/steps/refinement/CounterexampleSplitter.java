package hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.splittingcegar.common.data.KripkeStructure;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.interpolating.data.Interpolant;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractState;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractSystem;

/**
 * State splitter that cuts only states that are in the abstract counterexample.
 * Using a binary interpolant, only the failure state is split, but using a
 * sequence interpolant, multiple states can be split.
 *
 */
public class CounterexampleSplitter extends AbstractCEGARStep implements Splitter {

	public CounterexampleSplitter(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public int split(final InterpolatedAbstractSystem system, final List<InterpolatedAbstractState> abstractCounterEx,
			final Interpolant interpolant) {
		assert (0 < interpolant.size() && interpolant.size() <= abstractCounterEx.size());
		int firstSplit = -1;
		for (int i = 0; i < interpolant.size(); ++i) {
			if (stopHandler.isStopped())
				return 0;
			if (!interpolant.get(i).equals(True())) {
				splitSingleState(system, abstractCounterEx.get(i), interpolant.get(i));
				if (firstSplit == -1)
					firstSplit = i;
			}
		}
		assert (0 <= firstSplit && firstSplit < abstractCounterEx.size());
		return firstSplit;
	}

	private void splitSingleState(final InterpolatedAbstractSystem system, final InterpolatedAbstractState stateToSplit,
			Expr<? extends BoolType> interpolant) {
		final STS sts = system.getSTS();

		final Solver solver = solvers.getSolver();

		final KripkeStructure<InterpolatedAbstractState> ks = system.getAbstractKripkeStructure();

		// Remove negations from the interpolant (to avoid multiple negations)
		while (interpolant instanceof NotExpr)
			interpolant = ((NotExpr) interpolant).getOp();

		logger.writeln("Refining " + stateToSplit, 5, 1);

		// Create refined abstract states using the interpolant and its negation
		final List<InterpolatedAbstractState> refinedStates = new ArrayList<>(2);
		refinedStates.add(stateToSplit.refine(interpolant));
		refinedStates.add(stateToSplit.refine(Not(interpolant)));
		// Check for contradicting labels
		for (final InterpolatedAbstractState refined : refinedStates) {
			solver.push();
			SolverHelper.unrollAndAssert(solver, refined.getLabels(), sts, 0);
			final boolean check = SolverHelper.checkSat(solver);
			solver.pop();
			if (!check) {
				logger.writeln("Cannot refine.", 5, 2);
				return;
			}
		}

		// Remove the original state
		ks.getStates().remove(stateToSplit);
		ks.getInitialStates().remove(stateToSplit);

		logger.writeln(refinedStates.size() + " new abstract states.", 5, 1);
		for (final InterpolatedAbstractState refined : refinedStates)
			logger.writeln(refined, 6, 2);

		// Check if the refined states are initial (only if the original state
		// was initial, but
		// then at least one of the refined states must also be initial -->
		// assertion)
		if (stateToSplit.isInitial()) {
			solver.push();
			solver.add(PathUtils.unfold(sts.getInit(), 0));
			boolean isInitial = false;
			for (final InterpolatedAbstractState refined : refinedStates) {
				solver.push();
				SolverHelper.unrollAndAssert(solver, refined.getLabels(), sts, 0);
				refined.setInitial(SolverHelper.checkSat(solver));
				if (refined.isInitial())
					isInitial = true;
				solver.pop();
			}
			assert (isInitial);
			solver.pop();
		}

		if (stopHandler.isStopped())
			return;

		// Get successors for the abstract states (only the successors of the
		// original state
		// have to be checked, but every successor must belong to at least one
		// of the
		// refined states --> assertion)
		solver.push();
		solver.add(PathUtils.unfold(sts.getTrans(), 0));
		for (final InterpolatedAbstractState succ : stateToSplit.getSuccessors()) {
			if (stopHandler.isStopped())
				return;
			if (succ.equals(stateToSplit))
				continue;
			// The failure state has to be removed from predecessors
			final boolean removed = succ.getPredecessors().remove(stateToSplit);
			assert (removed);
			solver.push();
			SolverHelper.unrollAndAssert(solver, succ.getLabels(), sts, 1);
			boolean isSuccessor = false;
			for (final InterpolatedAbstractState refined : refinedStates) {
				if (stopHandler.isStopped())
					return;
				solver.push();
				SolverHelper.unrollAndAssert(solver, refined.getLabels(), sts, 0);
				if (SolverHelper.checkSat(solver)) {
					refined.addSuccessor(succ);
					succ.addPredecessor(refined);
					isSuccessor = true;
				}
				solver.pop();
			}
			assert (isSuccessor);
			solver.pop();
		}

		// Get predecessors for the abstract states (only the predecessors of
		// the original state
		// have to be checked, but every predecessor must belong to at least one
		// of the
		// refined states --> assertion)
		for (final InterpolatedAbstractState prev : stateToSplit.getPredecessors()) {
			if (stopHandler.isStopped())
				return;
			if (prev.equals(stateToSplit))
				continue;
			final boolean removed = prev.getSuccessors().remove(stateToSplit);
			assert (removed);
			solver.push();
			SolverHelper.unrollAndAssert(solver, prev.getLabels(), sts, 0);
			boolean isPredecessor = false;
			for (final InterpolatedAbstractState refined : refinedStates) {
				if (stopHandler.isStopped())
					return;
				solver.push();
				SolverHelper.unrollAndAssert(solver, refined.getLabels(), sts, 1);
				if (SolverHelper.checkSat(solver)) {
					prev.addSuccessor(refined);
					refined.addPredecessor(prev);
					isPredecessor = true;
				}
				solver.pop();
			}
			solver.pop();
			assert (isPredecessor);
		}

		// Check transitions between refined states (only if the failure state
		// was a successor
		// of itself, but then at least one transition must also be present
		// between the
		// refined states --> assertion)
		if (stateToSplit.getSuccessors().contains(stateToSplit)) {
			boolean isSuccessor = false;
			for (final InterpolatedAbstractState ref0 : refinedStates) {
				if (stopHandler.isStopped())
					return;
				solver.push();
				SolverHelper.unrollAndAssert(solver, ref0.getLabels(), sts, 0);
				for (final InterpolatedAbstractState ref1 : refinedStates) {
					if (stopHandler.isStopped())
						return;
					solver.push();
					SolverHelper.unrollAndAssert(solver, ref1.getLabels(), sts, 1);
					if (SolverHelper.checkSat(solver)) {
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
