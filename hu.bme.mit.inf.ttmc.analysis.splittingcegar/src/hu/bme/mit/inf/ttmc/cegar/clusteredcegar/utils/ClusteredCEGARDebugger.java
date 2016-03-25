package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ComponentAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.debugging.AbstractDebugger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.debugging.Debugger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

public class ClusteredCEGARDebugger extends AbstractDebugger implements Debugger<ClusteredAbstractSystem, ClusteredAbstractState> {
	private final Map<ClusteredAbstractState, List<ConcreteState>> stateSpace; // Abstract and concrete state space
	private final Set<ClusteredAbstractState> reachableStates; // Set of reachable states
	private AbstractSystem system = null;

	public ClusteredCEGARDebugger(final Visualizer visualizer) {
		super(visualizer);
		stateSpace = new HashMap<>();
		reachableStates = new HashSet<>();
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> explore(final ClusteredAbstractSystem system) {
		clearStateSpace();
		this.system = system;

		final STSUnroller unroller = system.getUnroller();
		final Solver solver = system.getManager().getSolverFactory().createSolver(true, false);

		// Explore all abstract states
		ClusteredAbstractState nextCAS = null;
		final int[] prev = new int[system.getAbstractKripkeStructures().size()];
		prev[0] = -1;
		for (int i = 1; i < prev.length; ++i)
			prev[i] = 0;
		do {
			nextCAS = getNextState(system, prev, solver, unroller);
			if (nextCAS != null)
				stateSpace.put(nextCAS, new ArrayList<>());
		} while (nextCAS != null);

		// Explore corresponding concrete states
		final Collection<ConcreteState> allConcreteStates = new ArrayList<>(); // Also store them temporary in a flat collection
		solver.push(); // 1
		solver.add(unroller.inv(0));
		for (final ClusteredAbstractState cas : stateSpace.keySet()) {
			solver.push(); // 2
			for (final ComponentAbstractState as : cas.getStates())
				for (final Expr<? extends BoolType> label : as.getLabels())
					solver.add(unroller.unroll(label, 0));
			do {
				if (SolverHelper.checkSat(solver)) {
					final Expr<? extends BoolType> csExpr = unroller.getConcreteState(solver.getModel(), 0, system.getVars());
					final ConcreteState cs = new ConcreteState(csExpr);
					stateSpace.get(cas).add(cs);
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
		for (final ClusteredAbstractState cas0 : stateSpace.keySet()) {
			solver.push(); // 3
			for (final ComponentAbstractState as : cas0.getStates())
				for (final Expr<? extends BoolType> label : as.getLabels())
					solver.add(unroller.unroll(label, 0));
			for (final ClusteredAbstractState cas1 : stateSpace.keySet()) {
				solver.push(); // 4
				for (final ComponentAbstractState as : cas1.getStates())
					for (final Expr<? extends BoolType> label : as.getLabels())
						solver.add(unroller.unroll(label, 1));
				if (SolverHelper.checkSat(solver))
					cas0.getSuccessors().add(cas1);
				solver.pop(); // 4
			}
			solver.pop(); //3
		}
		solver.pop(); // 2
		solver.pop(); // 1

		// Explore reachable abstract states
		for (final ClusteredAbstractState cas0 : stateSpace.keySet()) {
			if (cas0.isInitial()) {
				final Stack<ClusteredAbstractState> stack = new Stack<>();
				stack.push(cas0);

				while (!stack.isEmpty()) {
					final ClusteredAbstractState actual = stack.pop();
					if (!reachableStates.contains(actual)) {
						reachableStates.add(actual);
						for (final ClusteredAbstractState next : actual.getSuccessors())
							stack.push(next);
					}
				}
			}
		}

		// Explore the transition relation between concrete states and initial states
		exploreConcrTransRelAndInits(allConcreteStates, solver, unroller);

		// Explore the reachable concrete states
		exploreReachableConcrStates(allConcreteStates);

		// Mark unsafe states
		markUnsafeStates(allConcreteStates, system.getManager().getExprFactory().Not(system.getSTS().getProp()), solver, unroller);

		return this;
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> clearStateSpace() {
		stateSpace.clear();
		reachableStates.clear();
		clearAbstractCE();
		clearConcreteTrace();
		return this;
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> setAbstractCE(final List<ClusteredAbstractState> ace) {
		if (stateSpace.isEmpty())
			throw new RuntimeException("State space is not explored");
		clearAbstractCE();
		for (final ClusteredAbstractState cas0 : ace)
			for (final ClusteredAbstractState cas1 : stateSpace.keySet())
				if (cas0.equals(cas1)) {
					cas1.setPartOfCounterexample(true);
					break;
				}

		return this;
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> clearAbstractCE() {
		for (final ClusteredAbstractState cas : stateSpace.keySet())
			cas.setPartOfCounterexample(false);
		return this;
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> setConcreteTrace(final ConcreteTrace cce) {
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
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> clearConcreteTrace() {
		for (final List<ConcreteState> csList : stateSpace.values())
			for (final ConcreteState cs : csList)
				cs.isPartOfCounterExample = false;
		return this;
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> visualize() {
		visualize(stateSpace, reachableStates, system.getManager());
		return this;
	}

	// Get the next abstract state in the product
	private ClusteredAbstractState getNextState(final ClusteredAbstractSystem system, final int[] previous, final Solver solver, final STSUnroller unroller) {
		previous[0]++;
		for (int i = 0; i < previous.length; ++i) {
			if (previous[i] == system.getAbstractKripkeStructure(i).getStates().size()) {
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

		boolean isInitial = true;
		for (int i = 0; i < previous.length; ++i)
			if (!system.getAbstractKripkeStructure(i).getState(previous[i]).isInitial()) {
				isInitial = false;
				break;
			}
		;

		// Check if state is really initial
		if (isInitial) {
			solver.push();
			for (int i = 0; i < previous.length; ++i)
				SolverHelper.unrollAndAssert(solver, system.getAbstractKripkeStructure(i).getState(previous[i]).getLabels(), unroller, 0);
			solver.add(unroller.init(0));
			isInitial = SolverHelper.checkSat(solver);
			solver.pop();
		}

		final ClusteredAbstractState ret = new ClusteredAbstractState(previous.length, isInitial);

		for (int i = 0; i < previous.length; ++i)
			ret.getStates()[i] = system.getAbstractKripkeStructure(i).getState(previous[i]);

		return ret;
	}
}
