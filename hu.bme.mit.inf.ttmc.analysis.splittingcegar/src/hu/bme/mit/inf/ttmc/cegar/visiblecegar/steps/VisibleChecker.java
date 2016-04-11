package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractResult;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Checker;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.utils.VisualizationHelper;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

public class VisibleChecker extends AbstractCEGARStep implements Checker<VisibleAbstractSystem, VisibleAbstractState> {

	public VisibleChecker(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public AbstractResult<VisibleAbstractState> check(final VisibleAbstractSystem system) {
		final Solver solver = system.getManager().getSolverFactory().createSolver(true, false);

		final NotExpr negProp = system.getManager().getExprFactory().Not(system.getSTS().getProp());

		final STS sts = system.getSTS();
		Stack<VisibleAbstractState> counterExample = null;
		// Store explored states in a map. The key and the value is the same state.
		// This is required because when a new state is created, it is a different object
		// and the original one can be retrieved from the map.
		final Map<VisibleAbstractState, VisibleAbstractState> exploredStates = new HashMap<>();

		VisibleAbstractState actualInit = null;
		final List<AndExpr> prevInits = new ArrayList<>();
		// Get the first initial state
		solver.push();
		solver.add(sts.unrollInv(0));
		solver.add(sts.unrollInit(0));
		if (SolverHelper.checkSat(solver))
			actualInit = new VisibleAbstractState(sts.getConcreteState(solver.getModel(), 0, system.getVisibleVars()), true);
		solver.pop();

		// Loop until there is a next initial state
		while (actualInit != null && counterExample == null) {
			if (isStopped)
				return null;
			final Stack<VisibleAbstractState> stateStack = new Stack<>();
			final Stack<List<VisibleAbstractState>> successorStack = new Stack<>();

			if (!exploredStates.containsKey(actualInit)) {
				logger.writeln("Initial state: " + actualInit, 5);
				exploredStates.put(actualInit, actualInit);
				// Push to stack and get successors
				stateStack.push(actualInit);
				successorStack.push(getSuccessors(actualInit, system, solver, sts));
				// Check if the specification holds
				if (checkState(actualInit, negProp, solver, sts)) {
					logger.writeln("Counterexample reached!", 5, 1);
					counterExample = stateStack;
				}
			}
			// TODO: else: mark existing state as initial state

			// Loop until the stack is empty or a counterexample is found
			while (!stateStack.empty() && counterExample == null) {
				if (isStopped)
					return null;
				// Get the next successor of the actual state (which is on top of stateStack)
				final int nextSucc = successorStack.peek().size() - 1;
				if (nextSucc >= 0) { // Get the next state (and also remove)
					final VisibleAbstractState nextState = successorStack.peek().remove(nextSucc);
					if (!exploredStates.containsKey(nextState)) { // If it is not explored yet
						logger.write("New state: ", 6, 1);
						logger.writeln(nextState, 6, 0);
						exploredStates.put(nextState, nextState);

						stateStack.peek().addSuccessor(nextState);
						stateStack.push(nextState);
						// The successors found here are not added to the actual state here, only when they are explored
						successorStack.push(getSuccessors(nextState, system, solver, sts));
						// Check if the specification holds
						if (checkState(nextState, negProp, solver, sts)) {
							logger.writeln("Counterexample reached!", 5, 1);
							counterExample = stateStack;
							break;
						}
					} else { // If it is already explored
						// Get the original instance and add to the actual as successor
						stateStack.peek().addSuccessor(exploredStates.get(nextState));
					}
				} else { // If the actual state has no more successors, then backtrack
					stateStack.pop();
					successorStack.pop();
				}
			}

			// Get next initial state
			prevInits.add(actualInit.getExpression());
			solver.push();
			solver.add(sts.unrollInv(0));
			solver.add(sts.unrollInit(0));
			solver.add(sts.unroll(system.getManager().getExprFactory().Not(system.getManager().getExprFactory().Or(prevInits)), 0));
			if (SolverHelper.checkSat(solver))
				actualInit = new VisibleAbstractState(sts.getConcreteState(solver.getModel(), 0, system.getVisibleVars()), true);
			else
				actualInit = null;
			solver.pop();
		}

		logger.writeln("Explored state space statistics:", 2);
		logger.writeln("States: " + exploredStates.size(), 2, 1);

		if (counterExample != null) {
			logger.writeln("Counterexample found (length: " + counterExample.size() + ")", 2);
			// Mark states on the stack and print counterexample
			for (final VisibleAbstractState vas : counterExample) {
				vas.setPartOfCounterExample(true);
				logger.writeln(vas, 4, 1);
			}
			VisualizationHelper.visualize(exploredStates.keySet(), visualizer, 4);
		} else {
			logger.writeln("Specification holds.", 2);
			VisualizationHelper.visualize(exploredStates.keySet(), visualizer, 6);
		}

		if (isStopped)
			return null;

		return counterExample == null ? new AbstractResult<VisibleAbstractState>(null, exploredStates.keySet(), exploredStates.size())
				: new AbstractResult<VisibleAbstractState>(counterExample, null, exploredStates.size());
	}

	// Get successors of an abstract state
	private List<VisibleAbstractState> getSuccessors(final VisibleAbstractState state, final VisibleAbstractSystem system, final Solver solver, final STS sts) {
		final List<VisibleAbstractState> successors = new ArrayList<>(); // List of successors
		solver.push();
		solver.add(sts.unrollInv(0));
		solver.add(sts.unrollInv(1));
		solver.add(sts.unrollTrans(0));
		solver.add(sts.unroll(state.getExpression(), 0));
		// Loop until a new successor is found
		do {
			if (isStopped)
				return new ArrayList<>();
			if (SolverHelper.checkSat(solver)) {
				// Get successor
				// TODO: check if initial (only for presentation purposes, since it may be found as a successor of some state first than as an initial state)
				final VisibleAbstractState succ = new VisibleAbstractState(sts.getConcreteState(solver.getModel(), 1, system.getVisibleVars()), false);
				successors.add(succ);
				// Force new successors
				solver.add(sts.unroll(system.getManager().getExprFactory().Not(succ.getExpression()), 1));
			} else
				break;
		} while (true);
		solver.pop();
		return successors;
	}

	private boolean checkState(final VisibleAbstractState state, final Expr<? extends BoolType> expr, final Solver solver, final STS sts) {
		solver.push();
		solver.add(sts.unroll(state.getExpression(), 0));
		solver.add(sts.unrollInv(0));
		solver.add(sts.unroll(expr, 0));
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	@Override
	public String toString() {
		return "";
	}
}
