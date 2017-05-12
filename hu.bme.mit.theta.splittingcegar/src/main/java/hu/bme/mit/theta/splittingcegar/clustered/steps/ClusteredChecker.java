package hu.bme.mit.theta.splittingcegar.clustered.steps;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.NotExpr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractState;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractSystem;
import hu.bme.mit.theta.splittingcegar.clustered.data.ComponentAbstractState;
import hu.bme.mit.theta.splittingcegar.clustered.utils.VisualizationHelper;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractResult;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.steps.Checker;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;

public class ClusteredChecker extends AbstractCEGARStep
		implements Checker<ClusteredAbstractSystem, ClusteredAbstractState> {

	public ClusteredChecker(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public AbstractResult<ClusteredAbstractState> check(final ClusteredAbstractSystem system) {
		checkNotNull(system);
		final NotExpr negProp = Exprs.Not(system.getSTS().getProp());

		final STS sts = system.getSTS();
		// Store explored states in a map. The key and the value is the same
		// state.
		// This is required because when a new state is created, it is a
		// different object
		// and the original one can be retrieved from the map.
		final Map<ClusteredAbstractState, ClusteredAbstractState> exploredStates = new HashMap<>();
		Stack<ClusteredAbstractState> counterExample = null; // Store the
																// counterexample
																// (if found)

		ClusteredAbstractState actualInit;
		// Initialize backtracking array for initial states to [-1, 0, 0, ...,
		// 0]
		final int[] prevInit = new int[system.getAbstractKripkeStructures().size()];
		prevInit[0] = -1;
		for (int i = 1; i < prevInit.length; ++i)
			prevInit[i] = 0;

		int arcs = 0, deletedArcs = 0;
		final Solver solver = solvers.getSolver();

		solver.push();

		// Loop through each initial state and do a search
		while ((actualInit = getNextInitialState(system, prevInit)) != null && counterExample == null) {
			if (stopHandler.isStopped())
				return null;
			// Check if the state is really initial
			if (!checkInit(actualInit, solver, sts))
				continue;
			// Create stacks for backtracking
			final Stack<ClusteredAbstractState> stateStack = new Stack<>();
			final Stack<int[]> successorStack = new Stack<>();

			logger.writeln("Initial state: " + actualInit, 5);
			if (!exploredStates.containsKey(actualInit)) {
				exploredStates.put(actualInit, actualInit);
				// Initialize successor array to [-1, 0, 0, ..., 0]
				final int[] ss = new int[system.getAbstractKripkeStructures().size()];
				ss[0] = -1;
				for (int i = 1; i < ss.length; ++i)
					ss[i] = 0;
				stateStack.push(actualInit);
				successorStack.push(ss);
				// Check if the specification holds
				if (checkProp(actualInit, negProp, solver, sts)) {
					logger.writeln("Counterexample reached!", 5, 1);
					counterExample = stateStack;
				}
			}

			while (!stateStack.empty() && counterExample == null) {
				if (stopHandler.isStopped())
					return null;
				final ClusteredAbstractState actualState = stateStack.peek();
				final ClusteredAbstractState nextState = getNextSuccessor(actualState, successorStack.peek());

				if (nextState != null) {
					// Check if it is really a successor using the solver
					if (checkTrans(actualState, nextState, solver, sts)) {
						arcs++;
						if (!exploredStates.containsKey(nextState)) {
							logger.write("New state: ", 6, 1);
							logger.writeln(nextState, 6, 0);
							exploredStates.put(nextState, nextState);
							actualState.getSuccessors().add(nextState);
							final int[] ss = new int[system.getAbstractKripkeStructures().size()];
							ss[0] = -1;
							for (int i = 1; i < ss.length; ++i)
								ss[i] = 0;
							stateStack.push(nextState);
							successorStack.push(ss);
							// Check if the specification holds
							if (checkProp(nextState, negProp, solver, sts)) {
								logger.writeln("Counterexample reached!", 5, 1);
								counterExample = stateStack;
								break;
							}
						} else {
							// Get the original instance and add to the actual
							// as successor
							actualState.getSuccessors().add(exploredStates.get(nextState));
						}
					} else {
						deletedArcs++;
					}
				} else { // If the actual state has no more successors, then
								// backtrack
					stateStack.pop();
					successorStack.pop();
				}
			}
		}
		solver.pop();

		logger.writeln("Explored state space statistics:", 2);
		logger.writeln("States: " + exploredStates.size(), 2, 1);
		logger.writeln("Arcs: " + arcs + " (deleted: " + deletedArcs + ")", 2, 1);

		if (counterExample != null) {
			logger.writeln("Counterexample found (length: " + counterExample.size() + ")", 2);
			// Mark states on the stack and print counterexample
			for (final ClusteredAbstractState cas : counterExample) {
				cas.setPartOfCounterexample(true);
				logger.writeln(cas, 4, 1);
			}
			VisualizationHelper.visualizeCompositeAbstractKripkeStructure(exploredStates.keySet(), visualizer, 4);
		} else {
			logger.writeln("Specification holds.", 2);
			VisualizationHelper.visualizeCompositeAbstractKripkeStructure(exploredStates.keySet(), visualizer, 6);
		}

		return counterExample == null
				? new AbstractResult<ClusteredAbstractState>(null, exploredStates.keySet(), exploredStates.size())
				: new AbstractResult<ClusteredAbstractState>(counterExample, null, exploredStates.size());
	}

	private boolean checkProp(final ClusteredAbstractState state, final Expr<? extends BoolType> expr,
			final Solver solver, final STS sts) {
		solver.push();
		for (final ComponentAbstractState as : state.getStates())
			SolverHelper.unrollAndAssert(solver, as.getLabels(), sts, 0);
		solver.add(PathUtils.unfold(expr, 0));
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	private boolean checkTrans(final ClusteredAbstractState s0, final ClusteredAbstractState s1, final Solver solver,
			final STS sts) {
		solver.push();
		for (final ComponentAbstractState as : s0.getStates())
			SolverHelper.unrollAndAssert(solver, as.getLabels(), sts, 0);

		for (final ComponentAbstractState as : s1.getStates())
			SolverHelper.unrollAndAssert(solver, as.getLabels(), sts, 1);

		solver.add(PathUtils.unfold(sts.getTrans(), 0));

		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	private boolean checkInit(final ClusteredAbstractState s, final Solver solver, final STS sts) {
		solver.push();
		for (final ComponentAbstractState as : s.getStates())
			SolverHelper.unrollAndAssert(solver, as.getLabels(), sts, 0);
		solver.add(PathUtils.unfold(sts.getInit(), 0));

		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	// Get the next initial state
	// For example if the system has 3 clusters with 2, 3 and 4 initial states,
	// there are 2*3*4 = 24 abstract initial states in the following order:
	// (0,0,0), (1,0,0), (0,1,0), (1,1,0), (0,2,0), (1,2,0), (0,0,1), ...,
	// (1,2,3)
	private ClusteredAbstractState getNextInitialState(final ClusteredAbstractSystem system, final int[] previous) {
		previous[0]++;
		for (int i = 0; i < previous.length; ++i) {
			if (previous[i] == system.getAbstractKripkeStructure(i).getInitialStates().size()) {
				if (i < previous.length - 1) {
					previous[i] = 0;
					previous[i + 1]++;
				} else {
					return null;
				}
			} else {
				break;
			}
		}

		final ClusteredAbstractState ret = new ClusteredAbstractState(previous.length, true);

		for (int i = 0; i < previous.length; ++i)
			ret.getStates()[i] = system.getAbstractKripkeStructure(i).getInitialState(previous[i]);

		return ret;
	}

	// Get the next successor (similarly to the initial states)
	private ClusteredAbstractState getNextSuccessor(final ClusteredAbstractState state, final int[] prevSuccessor) {
		prevSuccessor[0]++;
		for (int i = 0; i < prevSuccessor.length; ++i) {
			if (prevSuccessor[i] == state.getStates()[i].getSuccessors().size()) {
				if (i < prevSuccessor.length - 1) {
					prevSuccessor[i] = 0;
					prevSuccessor[i + 1]++;
				} else {
					return null;
				}
			} else {
				break;
			}
		}

		final ClusteredAbstractState ret = new ClusteredAbstractState(prevSuccessor.length);
		for (int i = 0; i < prevSuccessor.length; ++i)
			ret.getStates()[i] = state.getStates()[i].getSuccessors().get(prevSuccessor[i]);

		return ret;
	}

	@Override
	public String toString() {
		return "";
	}
}
