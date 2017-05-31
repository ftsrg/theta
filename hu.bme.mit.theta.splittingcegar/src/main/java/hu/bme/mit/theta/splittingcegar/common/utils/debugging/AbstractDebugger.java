package hu.bme.mit.theta.splittingcegar.common.utils.debugging;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractState;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractSystem;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.ClusterNode;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Node;

/**
 * Base class for debuggers.
 */
public abstract class AbstractDebugger<AbstractSystemType extends AbstractSystem, AbstractStateType extends AbstractState>
		implements Debugger<AbstractSystemType, AbstractStateType> {
	protected final Visualizer visualizer;
	protected SolverWrapper solvers;

	public AbstractDebugger(final SolverWrapper solvers, final Visualizer visualizer) {
		this.solvers = solvers;
		this.visualizer = visualizer;
	}

	protected void exploreConcrTransRelAndInits(final Collection<ConcreteState> concreteStates, final STS sts) {
		final Solver solver = solvers.getSolver();
		solver.push();
		// Loop through each state
		for (final ConcreteState cs0 : concreteStates) {
			// Assert its expression
			solver.push();
			solver.add(PathUtils.unfold(cs0.model.toExpr(), 0));
			// Check if it is initial
			solver.push();
			solver.add(PathUtils.unfold(sts.getInit(), 0));
			cs0.isInitial = SolverHelper.checkSat(solver);
			solver.pop();
			// Loop through other states to get successors
			for (final ConcreteState cs1 : concreteStates) {
				solver.push();
				solver.add(PathUtils.unfold(cs1.model.toExpr(), 1));
				solver.add(PathUtils.unfold(sts.getTrans(), 0));
				if (SolverHelper.checkSat(solver))
					cs0.successors.add(cs1);
				solver.pop();
			}
			solver.pop();
		}
		solver.pop();
	}

	protected void exploreReachableConcrStates(final Collection<ConcreteState> concreteStates) {
		for (final ConcreteState cs0 : concreteStates) {
			if (cs0.isInitial) { // Start a search from each initial state
				final Stack<ConcreteState> stack = new Stack<>();
				stack.push(cs0);

				while (!stack.isEmpty()) {
					final ConcreteState actual = stack.pop();
					if (!actual.isReachable) {
						actual.isReachable = true;
						for (final ConcreteState next : actual.successors)
							stack.push(next);
					}
				}
			}
		}
	}

	protected void markUnsafeStates(final Collection<ConcreteState> concreteStates,
			final Expr<? extends BoolType> unsafeExpr, final STS sts) {
		final Solver solver = solvers.getSolver();
		solver.push();
		solver.add(PathUtils.unfold(unsafeExpr, 0));
		for (final ConcreteState cs0 : concreteStates) {
			solver.push();
			solver.add(PathUtils.unfold(cs0.model.toExpr(), 0));
			if (SolverHelper.checkSat(solver))
				cs0.isUnsafe = true;
			solver.pop();
		}
		solver.pop();
	}

	protected void visualize(final Map<? extends AbstractState, ? extends Collection<ConcreteState>> stateSpace,
			final Collection<? extends AbstractState> reachableStates) {
		if (stateSpace.isEmpty())
			throw new RuntimeException("State space is not explored.");

		final Map<AbstractState, Integer> ids = new HashMap<>();
		int id = 0;
		for (final AbstractState as : stateSpace.keySet()) {
			ids.put(as, id);
			++id;
		}

		final Graph g = new Graph("SYSTEM", "SYSTEM");
		for (final AbstractState as : stateSpace.keySet()) {
			final StringBuilder labelString = new StringBuilder("");
			final Expr<? extends BoolType> labelExpr = as.createExpression();
			if (labelExpr instanceof AndExpr) {
				for (final Expr<?> label : ((AndExpr) labelExpr).getOps())
					labelString.append(label).append(System.lineSeparator());
			} else {
				labelString.append(labelExpr);
			}

			final ClusterNode cn = new ClusterNode(("cluster_cas_" + ids.get(as)).replace('-', '_'),
					labelString.toString(), reachableStates.contains(as) ? "black" : "gray",
					as.isPartOfCounterexample() ? "pink" : "white", "", as.isInitial());
			g.addNode(cn);
			for (final AbstractState as1 : as.getSuccessors())
				cn.addSuccessor(("cluster_cas_" + ids.get(as1)).replace('-', '_'), "");

			for (final ConcreteState cs0 : stateSpace.get(as)) {
				final Node n = new Node("cs_" + cs0.createId(), cs0.toString(), (cs0.isReachable ? "" : "grey"),
						(cs0.isPartOfCounterExample ? "red" : ""), (cs0.isUnsafe ? "dashed" : ""), cs0.isInitial);
				cn.addSubNode(n);
				for (final ConcreteState cs1 : cs0.successors)
					n.addSuccessor("cs_" + cs1.createId(), (cs0.isPartOfCounterExample && cs1.isPartOfCounterExample
							&& cs0.counterExampleIndex < cs1.counterExampleIndex ? "red" : ""));
			}
		}

		visualizer.visualize(g);
	}

	/**
	 * Helper structure for storing concrete states
	 */
	protected static class ConcreteState {
		public Valuation model;
		public List<ConcreteState> successors;
		public int id;
		private static int nextId = 0;
		public boolean isInitial;
		public boolean isPartOfCounterExample;
		public int counterExampleIndex;
		public boolean isReachable;
		public boolean isUnsafe;

		public ConcreteState(final Valuation model) {
			this.model = model;
			this.id = nextId++;
			this.isInitial = false;
			this.isPartOfCounterExample = false;
			this.isReachable = false;
			this.isUnsafe = false;
			successors = new ArrayList<>();
		}

		@Override
		public String toString() {
			return model.toString();
		}

		public String createId() {
			return id + "";
		}

		@Override
		public boolean equals(final Object obj) {
			if (obj == null)
				return false;
			if (!(obj instanceof ConcreteState))
				return false;

			return ((ConcreteState) obj).model.equals(this.model);
		}

		@Override
		public int hashCode() {
			return this.model.hashCode();
		}
	}
}
