package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.debugging.DebuggerBase;
import hu.bme.mit.inf.ttmc.cegar.common.utils.debugging.IDebugger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

public class InterpolatingCEGARDebugger extends DebuggerBase implements IDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> {

	private final Map<InterpolatedAbstractState, List<ConcreteState>> stateSpace;
	private final Set<InterpolatedAbstractState> reachableStates;
	private IAbstractSystem system = null;

	public InterpolatingCEGARDebugger(final IVisualizer visualizer) {
		super(visualizer);

		stateSpace = new HashMap<>();
		reachableStates = new HashSet<>();
	}

	@Override
	public IDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> explore(final InterpolatedAbstractSystem system) {
		if (system.getAbstractKripkeStructure() == null)
			throw new RuntimeException("Abstract state space must be explored by the algorithm before exploring the concrete state space.");

		this.system = system;

		// Collect abstract states
		for (final InterpolatedAbstractState as : system.getAbstractKripkeStructure().getStates())
			stateSpace.put(as, new ArrayList<>());

		final STSUnroller unroller = system.getUnroller();
		final Solver solver = system.getManager().getSolverFactory().createSolver(true, false);

		// Explore corresponding concrete states
		final Collection<ConcreteState> allConcreteStates = new ArrayList<>(); // Also store them temporary in a flat collection
		solver.push(); // 1
		solver.add(unroller.inv(0));
		for (final InterpolatedAbstractState as : stateSpace.keySet()) {
			solver.push(); // 2
			SolverHelper.unrollAndAssert(solver, as.getLabels(), unroller, 0);
			do {
				if (SolverHelper.checkSatisfiable(solver)) {
					final Expr<? extends BoolType> csExpr = unroller.getConcreteState(solver.getModel(), 0, system.getVariables());
					final ConcreteState cs = new ConcreteState(csExpr);
					stateSpace.get(as).add(cs);
					allConcreteStates.add(cs);
					solver.add(unroller.unroll(system.getManager().getExprFactory().Not(csExpr), 0));
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

		// Explore the transition relation between concrete states and initial states
		exploreConcreteTransitionRelationAndInitials(allConcreteStates, solver, unroller);

		// Explore the reachable concrete states
		exploreReachableConcreteStates(allConcreteStates);

		// Mark unsafe states

		markUnsafeStates(allConcreteStates, system.getManager().getExprFactory().Not(system.getSystem().getProp()), solver, unroller);

		return this;
	}

	@Override
	public IDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> clearStateSpace() {
		stateSpace.clear();
		reachableStates.clear();
		clearAbstractCE();
		clearConcreteTrace();
		return this;
	}

	@Override
	public IDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> setAbstractCE(final List<InterpolatedAbstractState> ace) {
		if (stateSpace.isEmpty())
			throw new RuntimeException("State space is not explored");
		clearAbstractCE();
		// Interpolated abstract states are not constructed on-the-fly, thus
		// the given list contains the same objects as the explored state space
		// in the debugger. Since their attribute (isPartOfCounterexample) is
		// already set, only a check is required whether the state space is up-to-date
		for (final InterpolatedAbstractState as : ace) {
			if (!stateSpace.containsKey(as))
				throw new RuntimeException("A state in the counterexample is not included in the state space. The actual state space may not be up to date.");
		}
		return this;
	}

	@Override
	public IDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> clearAbstractCE() {
		clearConcreteTrace();
		// Interpolated abstract states are not constructed on-the-fly, thus
		// their isPartOfCounterExample attribute should be set to false by
		// the other parts of the algorithm
		return this;
	}

	@Override
	public IDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> setConcreteTrace(final ConcreteTrace cce) {
		if (stateSpace.isEmpty())
			throw new RuntimeException("State space is not explored");
		clearConcreteTrace();
		int ci = 0;
		for (final AndExpr m : cce.getTrace())
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
	public IDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> clearConcreteTrace() {
		for (final List<ConcreteState> csList : stateSpace.values())
			for (final ConcreteState cs : csList)
				cs.isPartOfCounterExample = false;
		return this;
	}

	@Override
	public IDebugger<InterpolatedAbstractSystem, InterpolatedAbstractState> visualize() {
		visualize(stateSpace, reachableStates, system.getManager());
		return this;
	}

}
