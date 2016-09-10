package hu.bme.mit.theta.splittingcegar.interpolating.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.formalism.common.Valuation;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.debugging.AbstractDebugger;
import hu.bme.mit.theta.splittingcegar.common.utils.debugging.Debugger;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractState;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractSystem;

public class InterpolatingCEGARDebugger extends AbstractDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> {

	private final Map<InterpolatedAbstractState, List<ConcreteState>> stateSpace;
	private final Set<InterpolatedAbstractState> reachableStates;

	public InterpolatingCEGARDebugger(final SolverWrapper solvers, final Visualizer visualizer) {
		super(solvers, visualizer);

		stateSpace = new HashMap<>();
		reachableStates = new HashSet<>();
	}

	@Override
	public Debugger<InterpolatedAbstractSystem, InterpolatedAbstractState> explore(final InterpolatedAbstractSystem system) {
		if (system.getAbstractKripkeStructure() == null)
			throw new RuntimeException("Abstract state space must be explored by the algorithm before exploring the concrete state space.");
		clearStateSpace();

		// Collect abstract states
		for (final InterpolatedAbstractState as : system.getAbstractKripkeStructure().getStates())
			stateSpace.put(as, new ArrayList<>());

		final STS sts = system.getSTS();

		// Explore corresponding concrete states
		// Also store them temporary in a flat collection
		final Collection<ConcreteState> allConcreteStates = new ArrayList<>();

		final Solver solver = solvers.getSolver();

		solver.push(); // 1
		solver.add(sts.unrollInv(0));
		for (final InterpolatedAbstractState as : stateSpace.keySet()) {
			solver.push(); // 2
			SolverHelper.unrollAndAssert(solver, as.getLabels(), sts, 0);
			do {
				if (SolverHelper.checkSat(solver)) {
					final Valuation csExpr = sts.getConcreteState(solver.getModel(), 0, system.getVars());

					final ConcreteState cs = new ConcreteState(csExpr);
					stateSpace.get(as).add(cs);
					allConcreteStates.add(cs);
					solver.add(sts.unroll(Exprs.Not(csExpr.toExpr()), 0));
				} else {
					break;
				}
			} while (true);
			solver.pop(); // 2
		}
		solver.pop(); // 1

		// Explore reachable abstract states
		for (final InterpolatedAbstractState as0 : stateSpace.keySet()) {
			if (as0.isInitial()) {
				final Stack<InterpolatedAbstractState> stack = new Stack<>();
				stack.push(as0);

				while (!stack.isEmpty()) {
					final InterpolatedAbstractState actual = stack.pop();
					if (!reachableStates.contains(actual)) {
						reachableStates.add(actual);
						for (final InterpolatedAbstractState next : actual.getSuccessors())
							stack.push(next);
					}
				}
			}
		}

		// Explore the transition relation between concrete states and initial
		// states
		exploreConcrTransRelAndInits(allConcreteStates, sts);

		// Explore the reachable concrete states
		exploreReachableConcrStates(allConcreteStates);

		// Mark unsafe states
		markUnsafeStates(allConcreteStates, Exprs.Not(system.getSTS().getProp()), sts);

		return this;
	}

	@Override
	public Debugger<InterpolatedAbstractSystem, InterpolatedAbstractState> clearStateSpace() {
		stateSpace.clear();
		reachableStates.clear();
		clearAbstractCE();
		clearConcreteTrace();
		return this;
	}

	@Override
	public Debugger<InterpolatedAbstractSystem, InterpolatedAbstractState> setAbstractCE(final List<InterpolatedAbstractState> ace) {
		if (stateSpace.isEmpty())
			throw new RuntimeException("State space is not explored");
		clearAbstractCE();
		// Interpolated abstract states are not constructed on-the-fly, thus
		// the given list contains the same objects as the explored state space
		// in the debugger. Since their attribute (isPartOfCounterexample) is
		// already set, only a check is required whether the state space is
		// up-to-date
		for (final InterpolatedAbstractState as : ace) {
			if (!stateSpace.containsKey(as))
				throw new RuntimeException("A state in the counterexample is not included in the state space. The actual state space may not be up to date.");
		}
		return this;
	}

	@Override
	public Debugger<InterpolatedAbstractSystem, InterpolatedAbstractState> clearAbstractCE() {
		clearConcreteTrace();
		// Interpolated abstract states are not constructed on-the-fly, thus
		// their isPartOfCounterExample attribute should be set to false by
		// the other parts of the algorithm
		return this;
	}

	@Override
	public Debugger<InterpolatedAbstractSystem, InterpolatedAbstractState> setConcreteTrace(final ConcreteTrace cce) {
		if (stateSpace.isEmpty())
			throw new RuntimeException("State space is not explored");
		clearConcreteTrace();
		int ci = 0;
		for (final Valuation m : cce.getTrace())
			for (final List<ConcreteState> csList : stateSpace.values())
				for (final ConcreteState cs : csList)
					if (m.equals(cs.model)) {
						cs.counterExampleIndex = ci++;
						cs.isPartOfCounterExample = true;
						break;
					}
		return this;
	}

	@Override
	public Debugger<InterpolatedAbstractSystem, InterpolatedAbstractState> clearConcreteTrace() {
		for (final List<ConcreteState> csList : stateSpace.values())
			for (final ConcreteState cs : csList)
				cs.isPartOfCounterExample = false;
		return this;
	}

	@Override
	public Debugger<InterpolatedAbstractSystem, InterpolatedAbstractState> visualize() {
		visualize(stateSpace, reachableStates);
		return this;
	}

}
