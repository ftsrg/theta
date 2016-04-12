package hu.bme.mit.inf.ttmc.cegar.common.utils.debugging;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.ClusterNode;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Node;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.solver.Solver;

/**
 * Base class for debuggers.
 */
public class AbstractDebugger {
	protected Visualizer visualizer;

	public AbstractDebugger(final Visualizer visualizer) {
		this.visualizer = visualizer;
	}

	protected void exploreConcrTransRelAndInits(final Collection<ConcreteState> concreteStates, final Solver solver,
			final STSUnroller unroller) {
		solver.push();
		solver.add(unroller.inv(0));
		// Loop through each state
		for (final ConcreteState cs0 : concreteStates) {
			// Assert its expression
			solver.push();
			solver.add(unroller.unroll(cs0.model, 0));
			// Check if it is initial
			solver.push();
			solver.add(unroller.init(0));
			cs0.isInitial = SolverHelper.checkSat(solver);
			solver.pop();
			// Loop through other states to get successors
			for (final ConcreteState cs1 : concreteStates) {
				solver.push();
				solver.add(unroller.inv(1));
				solver.add(unroller.unroll(cs1.model, 1));
				solver.add(unroller.trans(0));
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
			final Expr<? extends BoolType> unsafeExpr, final Solver solver, final STSUnroller unroller) {
		solver.push();
		solver.add(unroller.unroll(unsafeExpr, 0));
		for (final ConcreteState cs0 : concreteStates) {
			solver.push();
			solver.add(unroller.unroll(cs0.model, 0));
			if (SolverHelper.checkSat(solver))
				cs0.isUnsafe = true;
			solver.pop();
		}
		solver.pop();
	}

	protected void visualize(final Map<? extends AbstractState, ? extends Collection<ConcreteState>> stateSpace,
			final Collection<? extends AbstractState> reachableStates, final STSManager manager) {
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
			final Expr<? extends BoolType> labelExpr = as.createExpression(manager);
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
		public AndExpr model;
		public List<ConcreteState> successors;
		public int id;
		private static int nextId = 0;
		public boolean isInitial;
		public boolean isPartOfCounterExample;
		public int counterExampleIndex;
		public boolean isReachable;
		public boolean isUnsafe;

		public ConcreteState(final Expr<? extends BoolType> model) {
			this.model = (AndExpr) model;
			this.id = nextId++;
			this.isInitial = false;
			this.isPartOfCounterExample = false;
			this.isReachable = false;
			this.isUnsafe = false;
			successors = new ArrayList<ConcreteState>();
		}

		@Override
		public String toString() {
			return String.join(System.lineSeparator(),
					model.getOps().stream().map(m -> ((EqExpr) m).getLeftOp() + " = " + ((EqExpr) m).getRightOp())
							.collect(Collectors.toList()));
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
