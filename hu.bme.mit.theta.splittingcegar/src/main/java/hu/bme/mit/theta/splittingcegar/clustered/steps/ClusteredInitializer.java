package hu.bme.mit.theta.splittingcegar.clustered.steps;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.splittingcegar.clustered.data.Cluster;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractSystem;
import hu.bme.mit.theta.splittingcegar.clustered.data.ComponentAbstractState;
import hu.bme.mit.theta.splittingcegar.clustered.steps.clustering.ClusterCreator;
import hu.bme.mit.theta.splittingcegar.clustered.utils.VisualizationHelper;
import hu.bme.mit.theta.splittingcegar.common.data.KripkeStructure;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.steps.Initializer;
import hu.bme.mit.theta.splittingcegar.common.utils.FormulaCollector;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;

public class ClusteredInitializer extends AbstractCEGARStep implements Initializer<ClusteredAbstractSystem> {

	public ClusteredInitializer(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public ClusteredAbstractSystem create(final STS concrSys) {
		checkNotNull(concrSys);
		logger.write("Variables [" + concrSys.getVars().size() + "]:", 2);
		for (final VarDecl<? extends Type> varDecl : concrSys.getVars())
			logger.write(" " + varDecl.getName(), 3);
		logger.writeln(2);

		logger.writeln("Specification expression: " + concrSys.getProp(), 2);

		// Set ensures uniqueness
		final Set<Expr<? extends BoolType>> atomicFormulas = new HashSet<>();
		FormulaCollector.collectAtomsFromTransitionConditions(concrSys, atomicFormulas);
		FormulaCollector.collectAtomsFromExpression(concrSys.getProp(), atomicFormulas);

		final ClusteredAbstractSystem system = new ClusteredAbstractSystem(concrSys);
		system.getVars().addAll(concrSys.getVars());
		system.getAtomicFormulas().addAll(atomicFormulas);

		logger.writeln("Atomic formulas [" + system.getAtomicFormulas().size() + "]", 2);
		for (final Expr<? extends BoolType> ex : system.getAtomicFormulas())
			logger.writeln(ex, 3, 1);

		if (stopHandler.isStopped())
			return null;

		// Get clusters
		system.getClusters().addAll(new ClusterCreator().getClusters(system.getVars(), system.getAtomicFormulas()));
		logger.writeln("Clusters [" + system.getClusters().size() + "]", 2);
		for (final Cluster cluster : system.getClusters())
			logger.writeln(cluster, 3, 1);

		// Create Kripke structures

		system.getAbstractKripkeStructures().clear();
		final STS sts = system.getSTS();
		final Solver solver = solvers.getSolver();

		solver.push();
		solver.add(sts.unrollInv(0));
		// Loop through clusters and create abstract Kripke structures
		int c = 0;
		for (final Cluster cluster : system.getClusters()) {
			if (stopHandler.isStopped())
				return null;
			logger.write("Cluster " + c++, 2);

			system.getAbstractKripkeStructures().add(createAbstractKripkeStructure(cluster, sts));
		}
		solver.pop();
		// Visualize the abstract Kripke structures
		VisualizationHelper.visualizeAbstractKripkeStructures(system, visualizer, 4);

		return system;
	}

	private KripkeStructure<ComponentAbstractState> createAbstractKripkeStructure(final Cluster cluster,
			final STS sts) {
		final KripkeStructure<ComponentAbstractState> ks = new KripkeStructure<>();
		// If there is no formula for the cluster, add a default one
		if (cluster.getFormulas().size() == 0)
			cluster.getFormulas().add(Exprs.True());
		// Calculate negate for each formula
		final List<Expr<? extends BoolType>> negates = new ArrayList<>(cluster.getFormulas().size());
		for (final Expr<? extends BoolType> ex : cluster.getFormulas())
			negates.add(Exprs.Not(ex));

		// Traverse the possible abstract states. Each formula is either
		// unnegated or negated, so
		// there are 2^|formulas| possible abstract states. We start with an
		// empty state (no
		// formulas) and in each step we expand the state with the unnegated and
		// negated version
		// of the next formula, i.e., two new states may be obtained (if
		// feasible).
		final Stack<ComponentAbstractState> stack = new Stack<>();
		stack.push(new ComponentAbstractState(cluster)); // Start with no
															// formulas

		while (!stack.isEmpty()) {
			final ComponentAbstractState actual = stack.pop(); // Get the next
																// state

			// Add the next formula unnegated
			final ComponentAbstractState s1 = actual.cloneAndAdd(cluster.getFormulas().get(actual.getLabels().size()));

			if (isStateFeasible(s1, sts)) {
				// If the state is feasible and there are no more formulas, this
				// state is finished
				if (s1.getLabels().size() == cluster.getFormulas().size())
					ks.addState(s1);
				else
					stack.push(s1); // Otherwise continue expanding
			}

			// Add the next formula negated
			final ComponentAbstractState s2 = actual.cloneAndAdd(negates.get(actual.getLabels().size()));

			if (isStateFeasible(s2, sts)) {
				// If the state is feasible and there are no more formulas, this
				// state is finished
				if (s2.getLabels().size() == cluster.getFormulas().size())
					ks.addState(s2);
				else
					stack.push(s2); // Otherwise continue expanding
			}
		}

		// Calculate initial states and transition relation
		logger.writeln(", abstract states [" + ks.getStates().size() + "]", 2);
		for (final ComponentAbstractState s0 : ks.getStates()) { // Loop through
																	// the
																	// states
			s0.setInitial(isStateInit(s0, sts)); // Check whether it is
													// initial

			if (s0.isInitial())
				ks.addInitialState(s0);

			for (final ComponentAbstractState s1 : ks.getStates()) // Calculate
																	// successors
				if (isTransFeasible(s0, s1, sts))

					s0.getSuccessors().add(s1);
			logger.writeln(s0, 4, 1);
		}

		return ks;
	}

	private boolean isStateFeasible(final ComponentAbstractState s, final STS sts) {
		final Solver solver = solvers.getSolver();
		solver.push();
		SolverHelper.unrollAndAssert(solver, s.getLabels(), sts, 0);
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	private boolean isStateInit(final ComponentAbstractState s, final STS sts) {
		final Solver solver = solvers.getSolver();
		solver.push();
		SolverHelper.unrollAndAssert(solver, s.getLabels(), sts, 0);
		solver.add(sts.unrollInit(0));
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	private boolean isTransFeasible(final ComponentAbstractState s0, final ComponentAbstractState s1, final STS sts) {
		final Solver solver = solvers.getSolver();
		solver.push();
		SolverHelper.unrollAndAssert(solver, s0.getLabels(), sts, 0);
		SolverHelper.unrollAndAssert(solver, s1.getLabels(), sts, 1);
		solver.add(sts.unrollTrans(0));
		solver.add(sts.unrollInv(1));
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	@Override
	public String toString() {
		return "";
	}
}
