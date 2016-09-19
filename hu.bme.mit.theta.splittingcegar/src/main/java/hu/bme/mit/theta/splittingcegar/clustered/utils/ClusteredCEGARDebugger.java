package hu.bme.mit.theta.splittingcegar.clustered.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractState;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractSystem;
import hu.bme.mit.theta.splittingcegar.clustered.data.ComponentAbstractState;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.debugging.AbstractDebugger;
import hu.bme.mit.theta.splittingcegar.common.utils.debugging.Debugger;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;

public class ClusteredCEGARDebugger extends AbstractDebugger<ClusteredAbstractSystem, ClusteredAbstractState> {
	private final Map<ClusteredAbstractState, List<ConcreteState>> stateSpace; // Abstract
																				// and
																				// concrete
																				// state
																				// space
	private final Set<ClusteredAbstractState> reachableStates; // Set of
																// reachable
																// states

	public ClusteredCEGARDebugger(final SolverWrapper solvers, final Visualizer visualizer) {
		super(solvers, visualizer);
		stateSpace = new HashMap<>();
		reachableStates = new HashSet<>();
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> explore(final ClusteredAbstractSystem system) {
		clearStateSpace();

		final STS sts = system.getSTS();
		final Solver solver = solvers.getSolver();

		// Explore all abstract states
		ClusteredAbstractState nextCAS = null;
		final int[] prev = new int[system.getAbstractKripkeStructures().size()];
		prev[0] = -1;
		for (int i = 1; i < prev.length; ++i)
			prev[i] = 0;
		do {
			nextCAS = getNextState(system, prev, solver, sts);
			if (nextCAS != null)
				stateSpace.put(nextCAS, new ArrayList<>());
		} while (nextCAS != null);

		// Explore corresponding concrete states
		final Collection<ConcreteState> allConcreteStates = new ArrayList<>(); // Also
																				// store
																				// them
																				// temporary
																				// in
																				// a
																				// flat
																				// collection
		solver.push(); // 1
		solver.add(sts.unrollInv(0));
		for (final ClusteredAbstractState cas : stateSpace.keySet()) {
			solver.push(); // 2
			for (final ComponentAbstractState as : cas.getStates())
				for (final Expr<? extends BoolType> label : as.getLabels())
					solver.add(sts.unroll(label, 0));
			do {
				if (SolverHelper.checkSat(solver)) {
					final Valuation csExpr = sts.getConcreteState(solver.getModel(), 0, system.getVars());

					final ConcreteState cs = new ConcreteState(csExpr);
					stateSpace.get(cas).add(cs);
					allConcreteStates.add(cs);
					solver.add(sts.unroll(Exprs.Not(csExpr.toExpr()), 0));
				} else {
					break;
				}
			} while (true);
			solver.pop(); // 2
		}

		// Explore abstract transition relation
		solver.push(); // 2
		solver.add(sts.unrollInv(1));
		solver.add(sts.unrollTrans(0));
		for (final ClusteredAbstractState cas0 : stateSpace.keySet()) {
			solver.push(); // 3
			for (final ComponentAbstractState as : cas0.getStates())
				for (final Expr<? extends BoolType> label : as.getLabels())
					solver.add(sts.unroll(label, 0));
			for (final ClusteredAbstractState cas1 : stateSpace.keySet()) {
				solver.push(); // 4
				for (final ComponentAbstractState as : cas1.getStates())
					for (final Expr<? extends BoolType> label : as.getLabels())
						solver.add(sts.unroll(label, 1));
				if (SolverHelper.checkSat(solver))
					cas0.getSuccessors().add(cas1);
				solver.pop(); // 4
			}
			solver.pop(); // 3
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
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> clearStateSpace() {
		stateSpace.clear();
		reachableStates.clear();
		clearAbstractCE();
		clearConcreteTrace();
		return this;
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> setAbstractCE(
			final List<ClusteredAbstractState> ace) {
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
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> clearConcreteTrace() {
		for (final List<ConcreteState> csList : stateSpace.values())
			for (final ConcreteState cs : csList)
				cs.isPartOfCounterExample = false;
		return this;
	}

	@Override
	public Debugger<ClusteredAbstractSystem, ClusteredAbstractState> visualize() {
		visualize(stateSpace, reachableStates);
		return this;
	}

	// Get the next abstract state in the product
	private ClusteredAbstractState getNextState(final ClusteredAbstractSystem system, final int[] previous,
			final Solver solver, final STS sts) {

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
				SolverHelper.unrollAndAssert(solver,
						system.getAbstractKripkeStructure(i).getState(previous[i]).getLabels(), sts, 0);
			solver.add(sts.unrollInit(0));

			isInitial = SolverHelper.checkSat(solver);
			solver.pop();
		}

		final ClusteredAbstractState ret = new ClusteredAbstractState(previous.length, isInitial);

		for (int i = 0; i < previous.length; ++i)
			ret.getStates()[i] = system.getAbstractKripkeStructure(i).getState(previous[i]);

		return ret;
	}
}
