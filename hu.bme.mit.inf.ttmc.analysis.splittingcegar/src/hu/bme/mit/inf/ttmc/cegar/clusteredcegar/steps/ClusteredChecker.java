package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ComponentAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.utils.VisualizationHelper;
import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractResult;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IChecker;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.ILogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * Model checking (explicit) step.
 *
 * @author Akos
 */
public class ClusteredChecker extends CEGARStepBase implements IChecker<ClusteredAbstractSystem, ClusteredAbstractState> {

	public ClusteredChecker(final STSManager manager, final ILogger logger, final IVisualizer visualizer) {
		super(manager, logger, visualizer);
	}

	@Override
	public AbstractResult<ClusteredAbstractState> check(final ClusteredAbstractSystem system) {

		// Get the negate of the inner expression of G(...)
		final NotExpr negSpec = manager.getExprFactory().Not(system.getSystem().getProp());

		final STSUnroller unroller = system.getUnroller(); // Create an unroller for k=1
		// Store explored states in a map. The key and the value is the same state.
		// This is required because when a new state is created, it is a different object
		// and the original one can be retrieved from the map.
		final Map<ClusteredAbstractState, ClusteredAbstractState> exploredStates = new HashMap<>();
		Stack<ClusteredAbstractState> counterExample = null; // Store the counterexample (if found)

		ClusteredAbstractState init; // Actual initial state
		// Initialize backtracking array for initial states to [-1, 0, 0, ..., 0]
		final int[] prevInit = new int[system.getAbstractKripkeStructures().size()];
		prevInit[0] = -1;
		for (int i = 1; i < prevInit.length; ++i)
			prevInit[i] = 0;

		// Count arcs and deleted arcs
		int arcs = 0, deletedArcs = 0;

		solver.push();
		solver.add(unroller.inv(0)); // Assert invariants for k=0

		// Loop through each initial state and do a search
		while ((init = getNextInitialState(system, prevInit)) != null && counterExample == null) {
			if (isStopped)
				return null;
			// Check if the state is really initial
			if (!checkInitial(init, unroller))
				continue;
			// Create stacks for backtracking
			final Stack<ClusteredAbstractState> stateStack = new Stack<>();
			final Stack<int[]> successorStack = new Stack<>();

			logger.writeln("Initial state: " + init, 5);
			if (!exploredStates.containsKey(init)) {
				exploredStates.put(init, init);
				// Initialize successor array to [-1, 0, 0, ..., 0]
				final int[] ss = new int[system.getAbstractKripkeStructures().size()];
				ss[0] = -1;
				for (int i = 1; i < ss.length; ++i)
					ss[i] = 0;
				// Push to stack
				stateStack.push(init);
				successorStack.push(ss);
				// Check if the specification holds
				if (checkState(init, negSpec, unroller)) {
					logger.writeln("Counterexample reached!", 5, 1);
					counterExample = stateStack;
				}
			}

			// Loop until the stack is empty or a counterexample is found
			while (!stateStack.empty() && counterExample == null) {
				if (isStopped)
					return null;
				// Get the actual state
				final ClusteredAbstractState actualState = stateStack.peek();
				// Get the next successor of the actual state
				final ClusteredAbstractState nextState = getNextSuccessor(actualState, successorStack.peek());

				if (nextState != null) { // If it has one
					// Check if it is really a successor using the solver
					if (checkTransition(actualState, nextState, unroller)) {
						arcs++;
						// If this state is not yet explored, process it
						if (!exploredStates.containsKey(nextState)) {
							logger.write("New state: ", 6, 1);
							logger.writeln(nextState, 6, 0);
							exploredStates.put(nextState, nextState);
							// Add to the actual state as a successor
							actualState.getSuccessors().add(nextState);
							final int[] ss = new int[system.getAbstractKripkeStructures().size()];
							ss[0] = -1;
							for (int i = 1; i < ss.length; ++i)
								ss[i] = 0;
							// Push to stack
							stateStack.push(nextState);
							successorStack.push(ss);
							// Check if the specification holds
							if (checkState(nextState, negSpec, unroller)) {
								logger.writeln("Counterexample reached!", 5, 1);
								counterExample = stateStack;
								break;
							}
						} else { // If it is already explored
							// Get the original instance and add to the actual as successor
							actualState.getSuccessors().add(exploredStates.get(nextState));
						}
					} else {
						deletedArcs++;
					}
				} else { // If the actual state has no more successors, then backtrack
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
				logger.writeln(cas, 4, 1); // Print each state in the counterexample
			}
			VisualizationHelper.visualizeCompositeAbstractKripkeStructure(exploredStates.keySet(), visualizer, 4);
		} else {
			logger.writeln("Specification holds.", 2);
			VisualizationHelper.visualizeCompositeAbstractKripkeStructure(exploredStates.keySet(), visualizer, 6);
		}

		return counterExample == null ? new AbstractResult<ClusteredAbstractState>(null, exploredStates.keySet(), exploredStates.size())
				: new AbstractResult<ClusteredAbstractState>(counterExample, null, exploredStates.size());
	}

	/**
	 * Check if an expression is feasible for a state
	 *
	 * @param state
	 *            State
	 * @param expr
	 *            Expression
	 * @param unroller
	 *            Unroller
	 * @return True if the expression holds for the state, false otherwise
	 */
	private boolean checkState(final ClusteredAbstractState state, final Expr<? extends BoolType> expr, final STSUnroller unroller) {
		solver.push();
		for (final ComponentAbstractState as : state.getStates())
			SolverHelper.unrollAndAssert(solver, as.getLabels(), unroller, 0);
		solver.add(unroller.unroll(expr, 0));
		final boolean ret = SolverHelper.checkSatisfiable(solver);
		solver.pop();
		return ret;
	}

	/**
	 * Check if a transition between two states is feasible
	 *
	 * @param s0
	 *            From state
	 * @param s1
	 *            To state
	 * @param unroller
	 *            Unroller
	 * @return True if there is a transition from s0 to s1, false otherwise
	 */
	private boolean checkTransition(final ClusteredAbstractState s0, final ClusteredAbstractState s1, final STSUnroller unroller) {
		solver.push();
		for (final ComponentAbstractState as : s0.getStates())
			SolverHelper.unrollAndAssert(solver, as.getLabels(), unroller, 0);

		for (final ComponentAbstractState as : s1.getStates())
			SolverHelper.unrollAndAssert(solver, as.getLabels(), unroller, 1);

		solver.add(unroller.inv(1));
		solver.add(unroller.trans(0));

		final boolean ret = SolverHelper.checkSatisfiable(solver);
		solver.pop();
		return ret;
	}

	/**
	 * Check if a composite state is really initial. E.g. suppose that (x=0,y=0)
	 * and (x=1,y=1) are initial states. Then in the cluster of x, both x=0 and
	 * x=1 are initial states and similarly in the cluster of y, both y=0 and
	 * y=1. However, the composition (x=0,y=1) is not initial.
	 *
	 * @param s
	 * @param unroller
	 * @return
	 */
	private boolean checkInitial(final ClusteredAbstractState s, final STSUnroller unroller) {
		solver.push();
		for (final ComponentAbstractState as : s.getStates())
			SolverHelper.unrollAndAssert(solver, as.getLabels(), unroller, 0);
		solver.add(unroller.init(0));

		final boolean ret = SolverHelper.checkSatisfiable(solver);
		solver.pop();
		return ret;
	}

	// Get the next initial state
	// For example if the system has 3 clusters with 2, 3 and 4 initial states,
	// there are 2*3*4 = 24 abstract initial states in the following order:
	// (0,0,0), (1,0,0), (0,1,0), (1,1,0), (0,2,0), (1,2,0), (0,0,1), ..., (1,2,3)
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
