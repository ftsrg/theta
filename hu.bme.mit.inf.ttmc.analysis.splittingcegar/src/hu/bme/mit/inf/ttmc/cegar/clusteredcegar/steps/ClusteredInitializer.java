package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.Cluster;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ComponentAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.clustering.ClusterCreator;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.utils.VisualizationHelper;
import hu.bme.mit.inf.ttmc.cegar.common.data.KripkeStructure;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IInitializer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.FormulaCollector;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * Initial abstraction creator step.
 *
 * @author Akos
 */
public class ClusteredInitializer extends CEGARStepBase implements IInitializer<ClusteredAbstractSystem> {
	/**
	 * Initialize the step with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 */
	public ClusteredInitializer(final STSManager manager, final Logger logger, final IVisualizer visualizer) {
		super(manager, logger, visualizer);
	}

	@Override
	public ClusteredAbstractSystem create(final STS concrSys) {
		logger.writeln("Specification expression: " + concrSys.getProp(), 2);

		// Print variables
		logger.write("Variables [" + concrSys.getVars().size() + "]:", 2);
		for (final VarDecl<? extends Type> varDecl : concrSys.getVars())
			logger.write(" " + varDecl.getName(), 3);
		logger.writeln(2);

		// Collect atomic formulas to a set that ensures uniqueness for isomorphic expressions
		final Set<Expr<? extends BoolType>> atomicFormulas = new HashSet<>();

		// Collect atomic formulas from the conditions
		FormulaCollector.collectAtomsFromTransitionConditions(concrSys, atomicFormulas);
		// Collect atomic formulas from the specification
		FormulaCollector.collectAtomsFromExpression(concrSys.getProp(), atomicFormulas);

		// Move the collected formulas to a list for further use
		final List<Expr<? extends BoolType>> atomicFormulasList = new ArrayList<>(atomicFormulas);

		logger.writeln("Atomic formulas [" + atomicFormulasList.size() + "]", 2);
		for (final Expr<? extends BoolType> ex : atomicFormulasList)
			logger.writeln(ex, 3, 1);

		final ClusteredAbstractSystem system = new ClusteredAbstractSystem(concrSys, manager);

		system.getVariables().addAll(concrSys.getVars());

		system.getAtomicFormulas().addAll(atomicFormulasList);

		if (isStopped)
			return null;

		// Get clusters
		system.getClusters().addAll(new ClusterCreator().getClusters(system.getVariables(), system.getAtomicFormulas()));
		logger.writeln("Clusters [" + system.getClusters().size() + "]", 2);
		for (final Cluster cluster : system.getClusters())
			logger.writeln(cluster, 3, 1);

		// Create Kripke structures

		system.getAbstractKripkeStructures().clear(); // Clear existing Kripke structures
		final STSUnroller unroller = system.getUnroller(); // Create an unroller for k=1

		solver.push();
		solver.add(unroller.inv(0)); // Assert invariants for k=0
		// Loop through clusters and create abstract Kripke structures
		int c = 0;
		for (final Cluster cluster : system.getClusters()) {
			if (isStopped)
				return null;
			logger.write("Cluster " + c++, 2);
			system.getAbstractKripkeStructures().add(createAbstractKripkeStructure(cluster, unroller));
		}
		solver.pop();
		// Visualize the abstract Kripke structures
		VisualizationHelper.visualizeAbstractKripkeStructures(system, visualizer, 4);

		return system;
	}

	/**
	 * Create an abstract Kripke structure for a cluster
	 *
	 * @param cluster
	 *            Cluster
	 * @param unroller
	 *            System unroller
	 * @return Abstract Kripke structure
	 */
	private KripkeStructure<ComponentAbstractState> createAbstractKripkeStructure(final Cluster cluster, final STSUnroller unroller) {
		final KripkeStructure<ComponentAbstractState> ks = new KripkeStructure<>();
		// If there is no formula for the cluster, add a default one
		if (cluster.getFormulas().size() == 0)
			cluster.getFormulas().add(manager.getExprFactory().True());
		// Calculate negate for each formula
		final List<Expr<? extends BoolType>> negates = new ArrayList<>(cluster.getFormulas().size());
		for (final Expr<? extends BoolType> ex : cluster.getFormulas())
			negates.add(manager.getExprFactory().Not(ex));

		// Traverse the possible abstract states. Each formula is either unnegated or negated, so
		// there are 2^|formulas| possible abstract states. We start with an empty state (no
		// formulas) and in each step we expand the state with the unnegated and negated version
		// of the next formula, i.e., two new states may be obtained (if feasible).
		final Stack<ComponentAbstractState> stack = new Stack<>();
		stack.push(new ComponentAbstractState(cluster)); // Start with no formulas

		while (!stack.isEmpty()) {
			final ComponentAbstractState actual = stack.pop(); // Get the next state

			// Add the next formula unnegated
			final ComponentAbstractState s1 = actual.cloneAndAdd(cluster.getFormulas().get(actual.getLabels().size()));
			if (isStateFeasible(s1, unroller)) {
				// If the state is feasible and there are no more formulas, this state is finished
				if (s1.getLabels().size() == cluster.getFormulas().size())
					ks.addState(s1);
				else
					stack.push(s1); // Otherwise continue expanding
			}

			// Add the next formula negated
			final ComponentAbstractState s2 = actual.cloneAndAdd(negates.get(actual.getLabels().size()));
			if (isStateFeasible(s2, unroller)) {
				// If the state is feasible and there are no more formulas, this state is finished
				if (s2.getLabels().size() == cluster.getFormulas().size())
					ks.addState(s2);
				else
					stack.push(s2); // Otherwise continue expanding
			}
		}

		// Calculate initial states and transition relation
		logger.writeln(", abstract states [" + ks.getStates().size() + "]", 2);
		for (final ComponentAbstractState s0 : ks.getStates()) { // Loop through the states
			s0.setInitial(isStateInitial(s0, unroller)); // Check whether it is initial
			if (s0.isInitial())
				ks.addInitialState(s0);
			for (final ComponentAbstractState s1 : ks.getStates()) // Calculate successors
				if (isTransitionFeasible(s0, s1, unroller))
					s0.getSuccessors().add(s1);
			logger.writeln(s0, 4, 1);
		}

		return ks;
	}

	/**
	 * Helper function for checking whether a state is feasible
	 *
	 * @param s
	 *            State
	 * @param unroller
	 *            System unroller
	 * @return True if the state is feasible, false otherwise
	 */
	private boolean isStateFeasible(final ComponentAbstractState s, final STSUnroller unroller) {
		solver.push();
		SolverHelper.unrollAndAssert(solver, s.getLabels(), unroller, 0);
		final boolean ret = SolverHelper.checkSatisfiable(solver);
		solver.pop();
		return ret;
	}

	/**
	 * Helper function for checking whether a state is initial
	 *
	 * @param s
	 *            State
	 * @param unroller
	 *            System unroller
	 * @return True if the state is initial, false otherwise
	 */
	private boolean isStateInitial(final ComponentAbstractState s, final STSUnroller unroller) {
		solver.push();
		SolverHelper.unrollAndAssert(solver, s.getLabels(), unroller, 0);
		solver.add(unroller.init(0));
		final boolean ret = SolverHelper.checkSatisfiable(solver);
		solver.pop();
		return ret;
	}

	/**
	 * Helper function for checking whether a transition is present between s0
	 * and s1
	 *
	 * @param s0
	 *            From state
	 * @param s1
	 *            To state
	 * @param unroller
	 *            System unroller
	 * @return True if a transition is present between s0 and s1, false
	 *         otherwise
	 */
	private boolean isTransitionFeasible(final ComponentAbstractState s0, final ComponentAbstractState s1, final STSUnroller unroller) {
		solver.push();
		SolverHelper.unrollAndAssert(solver, s0.getLabels(), unroller, 0);
		SolverHelper.unrollAndAssert(solver, s1.getLabels(), unroller, 1);
		solver.add(unroller.trans(0));
		solver.add(unroller.inv(1));
		final boolean ret = SolverHelper.checkSatisfiable(solver);
		solver.pop();
		return ret;
	}

	@Override
	public String toString() {
		return "";
	}
}
