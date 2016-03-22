package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ComponentAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.KripkeStructure;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IRefiner;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;

/**
 * Refines the abstraction using the spurious counterexample.
 *
 * @author Akos
 */
public class ClusteredRefiner extends CEGARStepBase implements IRefiner<ClusteredAbstractSystem, ClusteredAbstractState> {

	/**
	 * Initialize the step with a solver, logger and visualizer
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 */
	public ClusteredRefiner(final Logger logger, final IVisualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public ClusteredAbstractSystem refine(final ClusteredAbstractSystem system, final List<ClusteredAbstractState> abstractCounterEx,
			final ConcreteTrace concreteTrace) {

		final Solver solver = system.getManager().getSolverFactory().createSolver(true, false);
		final int traceLength = concreteTrace.size();
		assert (1 <= traceLength && traceLength < abstractCounterEx.size());

		// The failure state is the last state in the abstract counterexample which
		// can be reached with a concrete path
		final ClusteredAbstractState failureState = abstractCounterEx.get(traceLength - 1);
		logger.writeln("Failure state: " + failureState, 4, 0);

		// Create an unroller for the size of the trace
		final STSUnroller unroller = system.getUnroller();

		// Get dead-end states
		final List<AndExpr> deadEndStates = getDeadEndStates(solver, system.getManager(), unroller, abstractCounterEx, traceLength);

		// Get bad states
		// TODO: bad states are not needed currently, they are collected only for debugging
		/* List<Model> badStates = */getBadStates(solver, system.getManager(), unroller, abstractCounterEx, traceLength);

		int clusterNo = -1;
		// Loop through each component of the failure state
		int newStates = 0;
		for (final ComponentAbstractState as : failureState.getStates()) {
			if (isStopped)
				return null;
			++clusterNo;
			logger.write("Refining component: ", 5, 2);
			logger.writeln(as, 5, 0);
			// Get concrete states in the abstract state (projected)
			final List<AndExpr> concreteStates = getConcreteStates(solver, system.getManager(), as, unroller);
			// Cannot refine if there is only one state
			if (concreteStates.size() == 1)
				continue;

			// Currently every concrete state is in the same equivalence class. Refinement
			// means to partition this equivalence class into some smaller classes

			// For each state, collect the compatible states
			final List<List<AndExpr>> compatibility = new ArrayList<>(concreteStates.size());

			// Get variables outside the cluster
			final Set<VarDecl<? extends Type>> otherVars = new HashSet<>(system.getVariables());
			otherVars.removeAll(as.getCluster().getVariables());

			// Loop through pairs of states and check if they should be separated
			for (int i = 0; i < concreteStates.size(); ++i) {
				if (isStopped)
					return null;
				final List<AndExpr> comp = new ArrayList<>();
				comp.add(concreteStates.get(i)); // The state is compatible with itself
				for (int j = i + 1; j < concreteStates.size(); ++j) // Check other states
					if (checkPair(solver, as, concreteStates.get(i), concreteStates.get(j), deadEndStates, unroller, otherVars))
						comp.add(concreteStates.get(j));
				compatibility.add(comp);
			}

			// If the first state is compatible with every other, this means that  no
			// refinement is needed (every state stays in the same equivalence class
			if (compatibility.get(0).size() == concreteStates.size())
				continue;

			// Collect the new equivalence classes with their expressions
			final List<Expr<? extends BoolType>> eqclasses = new ArrayList<>();
			final Set<AndExpr> includedStates = new HashSet<>();
			// Loop through each state and if it was not included in an equivalence class yet,
			// then include it with its equivalence class
			for (int i = 0; i < compatibility.size(); ++i) {
				if (isStopped)
					return null;
				if (!includedStates.contains(concreteStates.get(i))) {
					if (compatibility.get(i).size() == 1) // If it is a single state -> expression of the state
						eqclasses.add(compatibility.get(i).get(0));
					else // If there are more states -> or expression of the expressions of the states
						eqclasses.add(system.getManager().getExprFactory().Or(compatibility.get(i)));

					for (final AndExpr cs : compatibility.get(i))
						includedStates.add(cs);
				}
			}

			assert (eqclasses.size() > 1);
			logger.writeln(eqclasses.size() + " new abstract states.", 5, 3);
			for (final Expr<? extends BoolType> ex : eqclasses)
				logger.writeln(ex, 7, 4);

			// Refine the abstract Kripke structure
			final KripkeStructure<ComponentAbstractState> ks = system.getAbstractKripkeStructure(clusterNo);

			// Remove the original state
			ks.getStates().remove(as);
			ks.getInitialStates().remove(as);

			// Create refined abstract states from the equivalence classes
			final List<ComponentAbstractState> refinedStates = new ArrayList<>(eqclasses.size());
			int eqCounter = 0;
			for (final Expr<? extends BoolType> eqclass : eqclasses)
				refinedStates.add(as.refine(eqCounter++, eqclass));

			// Check if the refined states are initial (only if the original state was initial, but
			// then at least one of the refined states must also be initial --> assertion)
			if (as.isInitial()) {
				solver.push();
				solver.add(unroller.inv(0));
				solver.add(unroller.init(0));
				boolean isInitial = false;
				for (final ComponentAbstractState refined : refinedStates) {
					solver.push();
					SolverHelper.unrollAndAssert(solver, refined.getLabels(), unroller, 0);
					if (SolverHelper.checkSatisfiable(solver)) {
						refined.setInitial(true);
						isInitial = true;
					}
					solver.pop();
				}
				assert (isInitial);
				solver.pop();
			}

			// Get successors for the abstract states (only the successors of the original state
			// have to be checked, but every successor must belong to at least one of the
			// refined states --> assertion)
			solver.push();
			solver.add(unroller.inv(0));
			solver.add(unroller.inv(1));
			solver.add(unroller.trans(0));
			for (final ComponentAbstractState succ : as.getSuccessors()) {
				if (isStopped)
					return null;
				if (succ.equals(as))
					continue;
				solver.push();
				SolverHelper.unrollAndAssert(solver, succ.getLabels(), unroller, 1);
				boolean isSuccessor = false;
				for (final ComponentAbstractState refined : refinedStates) {
					solver.push();
					SolverHelper.unrollAndAssert(solver, refined.getLabels(), unroller, 0);
					if (SolverHelper.checkSatisfiable(solver)) {
						refined.getSuccessors().add(succ);
						isSuccessor = true;
					}
					solver.pop();
				}
				assert (isSuccessor);
				solver.pop();
			}

			// Check transitions between refined states
			for (final ComponentAbstractState ref0 : refinedStates) {
				if (isStopped)
					return null;
				solver.push();
				SolverHelper.unrollAndAssert(solver, ref0.getLabels(), unroller, 0);
				for (final ComponentAbstractState ref1 : refinedStates) {
					solver.push();
					SolverHelper.unrollAndAssert(solver, ref1.getLabels(), unroller, 1);
					if (SolverHelper.checkSatisfiable(solver))
						ref0.getSuccessors().add(ref1);
					solver.pop();
				}

				solver.pop();
			}

			// TODO: store predecessor states
			// Update other states' successors: if the original state was a successor, then remove it
			// and check which refined states are successors (at least one must be --> assertion)
			for (final ComponentAbstractState prev : ks.getStates()) {
				if (isStopped)
					return null;
				if (prev.getSuccessors().contains(as)) {
					boolean isSuccessor = false;
					prev.getSuccessors().remove(as);
					solver.push();
					SolverHelper.unrollAndAssert(solver, prev.getLabels(), unroller, 0);
					for (final ComponentAbstractState refined : refinedStates) {
						solver.push();
						SolverHelper.unrollAndAssert(solver, refined.getLabels(), unroller, 1);
						if (SolverHelper.checkSatisfiable(solver)) {
							prev.getSuccessors().add(refined);
							isSuccessor = true;
						}
						solver.pop();
					}
					assert (isSuccessor);
					solver.pop();
				}
			}
			solver.pop();

			// Add new states
			ks.getStates().addAll(refinedStates);
			for (final ComponentAbstractState refined : refinedStates)
				if (refined.isInitial())
					ks.addInitialState(refined);
			newStates += refinedStates.size();
		}

		assert (newStates > 0);

		return system;
	}

	/**
	 * Get dead-end states, i.e., concrete states in the failure state, which
	 * can be reached with a concrete path
	 *
	 * @param unroller
	 *            System unroller
	 * @param abstractCounterEx
	 *            Abstract counterexample
	 * @param traceLength
	 *            Length of the concrete trace
	 * @return List of dead-end states
	 */
	private List<AndExpr> getDeadEndStates(final Solver solver, final STSManager manager, final STSUnroller unroller,
			final List<ClusteredAbstractState> abstractCounterEx, final int traceLength) {
		final List<AndExpr> deadEndStates = new ArrayList<>();
		solver.push();
		solver.add(unroller.init(0)); // Assert initial conditions
		for (int i = 0; i < traceLength; ++i) {
			solver.add(unroller.inv(i)); // Invariants
			for (final ComponentAbstractState as : abstractCounterEx.get(i).getStates())
				for (final Expr<? extends BoolType> label : as.getLabels())
					solver.add(unroller.unroll(label, i)); // Labels
			if (i > 0)
				solver.add(unroller.trans(i - 1)); // Transition relation
		}

		do {
			if (SolverHelper.checkSatisfiable(solver)) {
				// Get dead-end state
				final AndExpr ds = unroller.getConcreteState(solver.getModel(), traceLength - 1);
				logger.write("Dead end state: ", 6, 1);
				logger.writeln(ds, 6, 0);
				deadEndStates.add(ds);

				// Exclude this state in order to get new dead end states
				solver.add(unroller.unroll(manager.getExprFactory().Not(ds), traceLength - 1));
			} else
				break;
		} while (true);

		solver.pop();
		return deadEndStates;
	}

	/**
	 * Get bad states, i.e., concrete states in the failure state, which have a
	 * (concrete) successor belonging to the (abstract) successor of the failure
	 * state.
	 *
	 * @param unroller
	 *            System unroller
	 * @param abstractCounterEx
	 *            Abstract counterexample
	 * @param traceLength
	 *            Length of the concrete trace
	 * @return List of bad states
	 */
	private List<AndExpr> getBadStates(final Solver solver, final STSManager manager, final STSUnroller unroller,
			final List<ClusteredAbstractState> abstractCounterEx, final int traceLength) {
		final List<AndExpr> badStates = new ArrayList<>();
		solver.push();
		solver.add(unroller.inv(0)); // Invariants
		solver.add(unroller.inv(1)); // Invariants
		// Failure state
		for (final ComponentAbstractState as : abstractCounterEx.get(traceLength - 1).getStates())
			for (final Expr<? extends BoolType> label : as.getLabels())
				solver.add(unroller.unroll(label, 0)); // Labels
		// Next state
		for (final ComponentAbstractState as : abstractCounterEx.get(traceLength).getStates())
			for (final Expr<? extends BoolType> label : as.getLabels())
				solver.add(unroller.unroll(label, 1)); // Labels
		solver.add(unroller.trans(0)); // Transition relation

		do {
			if (SolverHelper.checkSatisfiable(solver)) {
				// Get bad state
				final AndExpr bs = unroller.getConcreteState(solver.getModel(), 0);
				logger.write("Bad state: ", 6, 1);
				logger.writeln(bs, 6, 0);
				badStates.add(bs);

				// Exclude this state in order to get new dead end states
				solver.add(unroller.unroll(manager.getExprFactory().Not(bs), 0));
			} else
				break;
		} while (true);
		solver.pop();
		return badStates;
	}

	/**
	 * Get all concrete states of an abstract state projected to the variables
	 * of the cluster
	 *
	 * @param abstractState
	 *            Abstract state
	 * @param unroller
	 *            System unroller
	 * @return List of projected concrete states
	 */
	private List<AndExpr> getConcreteStates(final Solver solver, final STSManager manager, final ComponentAbstractState abstractState,
			final STSUnroller unroller) {
		final List<AndExpr> concreteStates = new ArrayList<>();
		solver.push();
		solver.add(unroller.inv(0));
		// Assert the labels of the state
		for (final Expr<? extends BoolType> label : abstractState.getLabels())
			solver.add(unroller.unroll(label, 0));
		do {
			if (SolverHelper.checkSatisfiable(solver)) {
				// Get the model and project
				final AndExpr cs = unroller.getConcreteState(solver.getModel(), 0, abstractState.getCluster().getVariables());
				concreteStates.add(cs);
				// Exclude this state to get new ones
				solver.add(unroller.unroll(manager.getExprFactory().Not(cs), 0));
				logger.write("Concrete state: ", 7, 3);
				logger.writeln(cs, 7, 0);
			} else
				break;
		} while (true);
		solver.pop();
		return concreteStates;
	}

	/**
	 * Check wheter a pair of concrete states can remain in the same equivalence
	 * class
	 *
	 * @param as
	 *            The abstract state where the concrete states belong to
	 * @param cs0
	 *            First concrete state
	 * @param cs1
	 *            Second concrete state
	 * @param deadEndStates
	 *            List of dead end states
	 * @param unroller
	 *            System unroller
	 * @return True if the states are compatible, false otherwise
	 */
	private boolean checkPair(final Solver solver, final ComponentAbstractState as, final AndExpr cs0, final AndExpr cs1, final List<AndExpr> deadEndStates,
			final STSUnroller unroller, final Set<VarDecl<? extends Type>> otherVars) {
		// Project the dead-end states and check if they are equal
		final List<AndExpr> proj0 = projectDeadEndStates(solver, as, cs0, deadEndStates, unroller, otherVars);
		final List<AndExpr> proj1 = projectDeadEndStates(solver, as, cs1, deadEndStates, unroller, otherVars);
		if (proj0.size() != proj1.size())
			return false;

		for (final AndExpr p0 : proj0) {
			boolean found = false;
			for (final AndExpr p1 : proj1) {
				if (p0.equals(p1)) {
					found = true;
					break;
				}
			}
			if (!found)
				return false;
		}

		return true;
	}

	/**
	 * Project the dead-end states to a concrete state (proj function on page
	 * 778).
	 *
	 * @param as
	 *            Abstract state where the concrete state belongs to
	 * @param cs
	 *            Concrete state
	 * @param deadEndStates
	 *            List of dead-end states
	 * @param unroller
	 *            System unroller
	 * @return Dead-end states projected
	 */
	private List<AndExpr> projectDeadEndStates(final Solver solver, final ComponentAbstractState as, final AndExpr cs, final List<AndExpr> deadEndStates,
			final STSUnroller unroller, final Set<VarDecl<? extends Type>> otherVars) {
		// Example: concrete state: (x=1,y=2)
		// The dead-end states are: (x=1,y=2,z=3), (x=1,y=3,z=2), (x=1,y=2,z=5)
		// The result is: (z=3), (z=5)

		final List<AndExpr> ret = new ArrayList<>();
		solver.push();
		solver.add(unroller.unroll(cs, 0));
		for (final AndExpr ds : deadEndStates) {
			solver.push();
			solver.add(unroller.unroll(ds, 0));
			if (SolverHelper.checkSatisfiable(solver))
				ret.add(unroller.getConcreteState(solver.getModel(), 0, otherVars));
			solver.pop();
		}
		solver.pop();
		return ret;
	}

	@Override
	public String toString() {
		return "";
	}
}
