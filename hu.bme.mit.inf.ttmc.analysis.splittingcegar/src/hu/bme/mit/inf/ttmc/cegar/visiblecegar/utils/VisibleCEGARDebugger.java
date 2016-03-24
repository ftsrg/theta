package hu.bme.mit.inf.ttmc.cegar.visiblecegar.utils;

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
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

public class VisibleCEGARDebugger extends DebuggerBase implements IDebugger<VisibleAbstractSystem, VisibleAbstractState> {
	private final Map<VisibleAbstractState, List<ConcreteState>> stateSpace;
	private final Set<VisibleAbstractState> reachableStates;
	private IAbstractSystem system = null;

	public VisibleCEGARDebugger(final IVisualizer visualizer) {
		super(visualizer);
		stateSpace = new HashMap<>();
		reachableStates = new HashSet<>();
	}

	@Override
	public IDebugger<VisibleAbstractSystem, VisibleAbstractState> explore(final VisibleAbstractSystem system) {
		clearStateSpace();
		this.system = system;

		// Explore all abstract states
		final STSUnroller unroller = system.getUnroller();
		final Solver solver = system.getManager().getSolverFactory().createSolver(true, false);
		solver.push(); // 1
		solver.add(unroller.inv(0));

		solver.push(); // 2
		do {
			if (SolverHelper.checkSatisfiable(solver)) { // New state found
				final AndExpr vasExpr = unroller.getConcreteState(solver.getModel(), 0, system.getVisibleVariables());
				final VisibleAbstractState vas = new VisibleAbstractState(vasExpr, false);
				stateSpace.put(vas, new ArrayList<>());
				// Exclude
				solver.add(unroller.unroll(system.getManager().getExprFactory().Not(vasExpr), 0));
			} else {
				break;
			}
		} while (true);
		solver.pop(); // 2

		// Check initial states
		solver.push(); // 2
		solver.add(unroller.init(0));
		for (final VisibleAbstractState vas : stateSpace.keySet()) {
			solver.push(); // 3
			solver.add(unroller.unroll(vas.getExpression(), 0));
			vas.setInitial(SolverHelper.checkSatisfiable(solver));
			solver.pop(); // 3
		}
		solver.pop(); // 2

		// Explore corresponding concrete states
		final Collection<ConcreteState> allConcreteStates = new ArrayList<>(); // Also store them temporary in a flat collection
		for (final VisibleAbstractState vas : stateSpace.keySet()) {
			solver.push(); // 2
			solver.add(unroller.unroll(vas.getExpression(), 0));
			do {
				if (SolverHelper.checkSatisfiable(solver)) { // New concrete state found
					final Expr<? extends BoolType> csExpr = unroller.getConcreteState(solver.getModel(), 0, system.getVariables());
					final ConcreteState cs = new ConcreteState(csExpr);
					stateSpace.get(vas).add(cs);
					allConcreteStates.add(cs);
					solver.add(unroller.unroll(system.getManager().getExprFactory().Not(csExpr), 0));
				} else {
					break;
				}
			} while (true);
			solver.pop(); // 2
		}

		// Explore abstract transition relation
		solver.push(); // 2
		solver.add(unroller.inv(1));
		solver.add(unroller.trans(0));
		for (final VisibleAbstractState vas0 : stateSpace.keySet()) {
			solver.push(); // 3
			solver.add(unroller.unroll(vas0.getExpression(), 0));
			for (final VisibleAbstractState vas1 : stateSpace.keySet()) {
				solver.push(); // 4
				solver.add(unroller.unroll(vas1.getExpression(), 1));
				if (SolverHelper.checkSatisfiable(solver))
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

		// Explore the transition relation between concrete states and initial states
		exploreConcreteTransitionRelationAndInitials(allConcreteStates, solver, unroller);

		// Explore the reachable concrete states
		exploreReachableConcreteStates(allConcreteStates);

		// Mark unsafe states
		markUnsafeStates(allConcreteStates, system.getManager().getExprFactory().Not(system.getSystem().getProp()), solver, unroller);

		return this;
	}

	@Override
	public IDebugger<VisibleAbstractSystem, VisibleAbstractState> clearStateSpace() {
		stateSpace.clear();
		reachableStates.clear();
		return this;
	}

	@Override
	public IDebugger<VisibleAbstractSystem, VisibleAbstractState> setAbstractCE(final List<VisibleAbstractState> ace) {
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
	public IDebugger<VisibleAbstractSystem, VisibleAbstractState> clearAbstractCE() {
		for (final VisibleAbstractState vas : stateSpace.keySet())
			vas.setPartOfCounterExample(false);
		return this;
	}

	@Override
	public IDebugger<VisibleAbstractSystem, VisibleAbstractState> setConcreteTrace(final ConcreteTrace cce) {
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
	public IDebugger<VisibleAbstractSystem, VisibleAbstractState> clearConcreteTrace() {
		for (final List<ConcreteState> csList : stateSpace.values())
			for (final ConcreteState cs : csList)
				cs.isPartOfCounterExample = false;
		return this;
	}

	@Override
	public IDebugger<VisibleAbstractSystem, VisibleAbstractState> visualize() {
		visualize(stateSpace, reachableStates, system.getManager());
		return this;
	}

}
