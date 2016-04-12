package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps;

import static com.google.common.base.Preconditions.checkNotNull;

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
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Initializer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.FormulaCollector;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class ClusteredInitializer extends AbstractCEGARStep implements Initializer<ClusteredAbstractSystem> {

	public ClusteredInitializer(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
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

		if (isStopped)
			return null;

		// Get clusters
		system.getClusters().addAll(new ClusterCreator().getClusters(system.getVars(), system.getAtomicFormulas()));
		logger.writeln("Clusters [" + system.getClusters().size() + "]", 2);
		for (final Cluster cluster : system.getClusters())
			logger.writeln(cluster, 3, 1);

		// Create Kripke structures

		system.getAbstractKripkeStructures().clear();
		final STS sts = system.getSTS();
		final Solver solver = system.getManager().getSolverFactory().createSolver(true, false);
		solver.push();
		solver.add(sts.unrollInv(0));
		// Loop through clusters and create abstract Kripke structures
		int c = 0;
		for (final Cluster cluster : system.getClusters()) {
			if (isStopped)
				return null;
			logger.write("Cluster " + c++, 2);

			system.getAbstractKripkeStructures()
					.add(createAbstractKripkeStructure(cluster, solver, system.getManager(), sts));
		}
		solver.pop();
		// Visualize the abstract Kripke structures
		VisualizationHelper.visualizeAbstractKripkeStructures(system, visualizer, 4);

		return system;
	}

	private KripkeStructure<ComponentAbstractState> createAbstractKripkeStructure(final Cluster cluster,
			final Solver solver, final STSManager manager, final STS sts) {
		final KripkeStructure<ComponentAbstractState> ks = new KripkeStructure<>();
		// If there is no formula for the cluster, add a default one
		if (cluster.getFormulas().size() == 0)
			cluster.getFormulas().add(manager.getExprFactory().True());
		// Calculate negate for each formula
		final List<Expr<? extends BoolType>> negates = new ArrayList<>(cluster.getFormulas().size());
		for (final Expr<? extends BoolType> ex : cluster.getFormulas())
			negates.add(manager.getExprFactory().Not(ex));

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

			if (isStateFeasible(s1, solver, sts)) {
				// If the state is feasible and there are no more formulas, this
				// state is finished
				if (s1.getLabels().size() == cluster.getFormulas().size())
					ks.addState(s1);
				else
					stack.push(s1); // Otherwise continue expanding
			}

			// Add the next formula negated
			final ComponentAbstractState s2 = actual.cloneAndAdd(negates.get(actual.getLabels().size()));

			if (isStateFeasible(s2, solver, sts)) {
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
			s0.setInitial(isStateInit(s0, solver, sts)); // Check whether it is
															// initial

			if (s0.isInitial())
				ks.addInitialState(s0);

			for (final ComponentAbstractState s1 : ks.getStates()) // Calculate
																	// successors
				if (isTransFeasible(s0, s1, solver, sts))

					s0.getSuccessors().add(s1);
			logger.writeln(s0, 4, 1);
		}

		return ks;
	}

	private boolean isStateFeasible(final ComponentAbstractState s, final Solver solver, final STS sts) {
		solver.push();
		SolverHelper.unrollAndAssert(solver, s.getLabels(), sts, 0);
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	private boolean isStateInit(final ComponentAbstractState s, final Solver solver, final STS sts) {
		solver.push();
		SolverHelper.unrollAndAssert(solver, s.getLabels(), sts, 0);
		solver.add(sts.unrollInit(0));
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	private boolean isTransFeasible(final ComponentAbstractState s0, final ComponentAbstractState s1,
			final Solver solver, final STS sts) {
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
