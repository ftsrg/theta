package hu.bme.mit.theta.splittingcegar.visible.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.debugging.AbstractDebugger;
import hu.bme.mit.theta.splittingcegar.common.utils.debugging.Debugger;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractState;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractSystem;

public class VisibleCEGARDebugger extends AbstractDebugger<VisibleAbstractSystem, VisibleAbstractState> {
	private final Map<VisibleAbstractState, List<ConcreteState>> stateSpace;
	private final Set<VisibleAbstractState> reachableStates;

	public VisibleCEGARDebugger(final SolverWrapper solvers, final Visualizer visualizer) {
		super(solvers, visualizer);
		stateSpace = new HashMap<>();
		reachableStates = new HashSet<>();
	}

	@Override
	public Debugger<VisibleAbstractSystem, VisibleAbstractState> explore(final VisibleAbstractSystem system) {
		clearStateSpace();

		final Solver solver = solvers.getSolver();

		// Explore all abstract states
		final STS sts = system.getSTS();
		solver.push(); // 1

		solver.push(); // 2
		do {
			if (SolverHelper.checkSat(solver)) { // New state found
				final Valuation vasExpr = sts.getConcreteState(solver.getModel(), 0, system.getVisibleVars());
				final VisibleAbstractState vas = new VisibleAbstractState(vasExpr, false);
				stateSpace.put(vas, new ArrayList<>());
				// Exclude
				solver.add(PathUtils.unfold(Exprs.Not(vasExpr.toExpr()), 0));
			} else {
				break;
			}
		} while (true);
		solver.pop(); // 2

		// Check initial states
		solver.push(); // 2
		solver.add(PathUtils.unfold(sts.getInit(), 0));
		for (final VisibleAbstractState vas : stateSpace.keySet()) {
			solver.push(); // 3
			solver.add(PathUtils.unfold(vas.getValuation().toExpr(), 0));
			vas.setInitial(SolverHelper.checkSat(solver));
			solver.pop(); // 3
		}
		solver.pop(); // 2

		// Explore corresponding concrete states
		// Also store them temporary in a flat collection
		final Collection<ConcreteState> allConcreteStates = new ArrayList<>();

		for (final VisibleAbstractState vas : stateSpace.keySet()) {
			solver.push(); // 2
			solver.add(PathUtils.unfold(vas.getValuation().toExpr(), 0));
			do {
				if (SolverHelper.checkSat(solver)) { // New concrete state found
					final Valuation csExpr = sts.getConcreteState(solver.getModel(), 0, system.getVars());

					final ConcreteState cs = new ConcreteState(csExpr);
					stateSpace.get(vas).add(cs);
					allConcreteStates.add(cs);
					solver.add(PathUtils.unfold(Exprs.Not(csExpr.toExpr()), 0));
				} else {
					break;
				}
			} while (true);
			solver.pop(); // 2
		}

		// Explore abstract transition relation
		solver.push(); // 2
		solver.add(PathUtils.unfold(sts.getTrans(), 0));
		for (final VisibleAbstractState vas0 : stateSpace.keySet()) {
			solver.push(); // 3
			solver.add(PathUtils.unfold(vas0.getValuation().toExpr(), 0));
			for (final VisibleAbstractState vas1 : stateSpace.keySet()) {
				solver.push(); // 4
				solver.add(PathUtils.unfold(vas1.getValuation().toExpr(), 1));
				if (SolverHelper.checkSat(solver))
					vas0.addSuccessor(vas1);
				solver.pop(); // 4
			}
			solver.pop(); // 3
		}
		solver.pop(); // 2
		solver.pop(); // 1

		// Explore reachable abstract states
		for (final VisibleAbstractState vas0 : stateSpace.keySet()) {
			if (vas0.isInitial()) {
				final Stack<VisibleAbstractState> stack = new Stack<>();
				stack.push(vas0);

				while (!stack.isEmpty()) {
					final VisibleAbstractState actual = stack.pop();
					if (!reachableStates.contains(actual)) {
						reachableStates.add(actual);
						for (final VisibleAbstractState next : actual.getSuccessors())
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
	public Debugger<VisibleAbstractSystem, VisibleAbstractState> clearStateSpace() {
		stateSpace.clear();
		reachableStates.clear();
		return this;
	}

	@Override
	public Debugger<VisibleAbstractSystem, VisibleAbstractState> setAbstractCE(final List<VisibleAbstractState> ace) {
		if (stateSpace.isEmpty())
			throw new RuntimeException("State space is not explored");
		clearAbstractCE();
		for (final VisibleAbstractState vas0 : ace)
			for (final VisibleAbstractState vas1 : stateSpace.keySet())
				if (vas0.equals(vas1)) {
					vas1.setPartOfCounterExample(true);
					break;
				}

		return this;
	}

	@Override
	public Debugger<VisibleAbstractSystem, VisibleAbstractState> clearAbstractCE() {
		for (final VisibleAbstractState vas : stateSpace.keySet())
			vas.setPartOfCounterExample(false);
		return this;
	}

	@Override
	public Debugger<VisibleAbstractSystem, VisibleAbstractState> setConcreteTrace(final ConcreteTrace cce) {
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
	public Debugger<VisibleAbstractSystem, VisibleAbstractState> clearConcreteTrace() {
		for (final List<ConcreteState> csList : stateSpace.values())
			for (final ConcreteState cs : csList)
				cs.isPartOfCounterExample = false;
		return this;
	}

	@Override
	public Debugger<VisibleAbstractSystem, VisibleAbstractState> visualize() {
		visualize(stateSpace, reachableStates);
		return this;
	}

}
