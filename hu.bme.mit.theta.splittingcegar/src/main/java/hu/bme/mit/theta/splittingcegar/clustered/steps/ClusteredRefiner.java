package hu.bme.mit.theta.splittingcegar.clustered.steps;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractState;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractSystem;
import hu.bme.mit.theta.splittingcegar.clustered.data.ComponentAbstractState;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.KripkeStructure;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.steps.Refiner;
import hu.bme.mit.theta.splittingcegar.common.utils.SolverHelper;
import hu.bme.mit.theta.splittingcegar.common.utils.StsUtils;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;

public class ClusteredRefiner extends AbstractCEGARStep
		implements Refiner<ClusteredAbstractSystem, ClusteredAbstractState> {

	public ClusteredRefiner(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public ClusteredAbstractSystem refine(final ClusteredAbstractSystem system,
			final List<ClusteredAbstractState> abstractCounterEx, final ConcreteTrace concreteTrace) {

		final int traceLength = concreteTrace.size();
		assert (1 <= traceLength && traceLength < abstractCounterEx.size());
		final Solver solver = solvers.getSolver();

		// The failure state is the last state in the abstract counterexample
		// which
		// can be reached with a concrete path
		final ClusteredAbstractState failureState = abstractCounterEx.get(traceLength - 1);
		logger.writeln("Failure state: " + failureState, 4, 0);

		final STS sts = system.getSTS();

		final List<Valuation> deadEndStates = getDeadEndStates(abstractCounterEx, traceLength, sts);

		// Bad states are not needed currently, they can be collected for
		// debugging
		/// List<Model> badStates = getBadStates(abstractCounterEx, traceLength,
		// solver, system.getManager(), sts);

		int clusterNo = -1;
		// Loop through each component of the failure state
		int newStates = 0;
		for (final ComponentAbstractState as : failureState.getStates()) {
			if (stopHandler.isStopped())
				return null;
			++clusterNo;
			logger.write("Refining component: ", 5, 2);
			logger.writeln(as, 5, 0);
			// Get concrete states in the abstract state (projected)
			final List<Valuation> concreteStates = getConcreteStatesOfAbstractState(as, sts);

			// Cannot refine if there is only one state
			if (concreteStates.size() == 1)
				continue;

			// Currently every concrete state is in the same equivalence class.
			// Refinement
			// means to partition this equivalence class into some smaller
			// classes

			// For each state, collect the compatible states
			final List<List<Expr<BoolType>>> compatibility = new ArrayList<>(concreteStates.size());

			// Get variables outside the cluster
			final Set<VarDecl<?>> otherVars = new HashSet<>(system.getVars());
			otherVars.removeAll(as.getCluster().getVars());

			// Loop through pairs of states and check if they should be
			// separated
			for (int i = 0; i < concreteStates.size(); ++i) {
				if (stopHandler.isStopped())
					return null;
				final List<Expr<BoolType>> comp = new ArrayList<>();
				comp.add(concreteStates.get(i).toExpr()); // The state is
															// compatible with
															// itself
				for (int j = i + 1; j < concreteStates.size(); ++j) // Check
																	// other
																	// states
					if (checkPair(as, concreteStates.get(i), concreteStates.get(j), deadEndStates, otherVars, solver,
							sts))

						comp.add(concreteStates.get(j).toExpr());
				compatibility.add(comp);
			}

			// If the first state is compatible with every other, this means
			// that no
			// refinement is needed (every state stays in the same equivalence
			// class
			if (compatibility.get(0).size() == concreteStates.size())
				continue;

			// Collect the new equivalence classes with their expressions
			final List<Expr<BoolType>> eqclasses = new ArrayList<>();
			final Set<Expr<BoolType>> includedStates = new HashSet<>();
			// Loop through each state and if it was not included in an
			// equivalence class yet,
			// then include it with its equivalence class
			for (int i = 0; i < compatibility.size(); ++i) {
				if (stopHandler.isStopped())
					return null;
				if (!includedStates.contains(concreteStates.get(i))) {
					if (compatibility.get(i).size() == 1) // If it is a single
															// state ->
															// expression of the
															// state
						eqclasses.add(compatibility.get(i).get(0));
					else // If there are more states -> or expression of the
							// expressions of the states
						eqclasses.add(Or(compatibility.get(i)));

					for (final Expr<BoolType> cs : compatibility.get(i))
						includedStates.add(cs);
				}
			}

			assert (eqclasses.size() > 1);
			logger.writeln(eqclasses.size() + " new abstract states.", 5, 3);
			for (final Expr<BoolType> ex : eqclasses)
				logger.writeln(ex, 7, 4);

			// Refine the abstract Kripke structure
			final KripkeStructure<ComponentAbstractState> ks = system.getAbstractKripkeStructure(clusterNo);

			// Remove the original state
			ks.getStates().remove(as);
			ks.getInitialStates().remove(as);

			// Create refined abstract states from the equivalence classes
			final List<ComponentAbstractState> refinedStates = new ArrayList<>(eqclasses.size());
			int eqCounter = 0;
			for (final Expr<BoolType> eqclass : eqclasses)
				refinedStates.add(as.refine(eqCounter++, eqclass));

			// Check if the refined states are initial (only if the original
			// state was initial, but
			// then at least one of the refined states must also be initial -->
			// assertion)
			if (as.isInitial()) {
				solver.push();
				solver.add(PathUtils.unfold(sts.getInit(), 0));
				boolean isInitial = false;
				for (final ComponentAbstractState refined : refinedStates) {
					solver.push();
					SolverHelper.unrollAndAssert(solver, refined.getLabels(), sts, 0);
					if (SolverHelper.checkSat(solver)) {
						refined.setInitial(true);
						isInitial = true;
					}
					solver.pop();
				}
				assert (isInitial);
				solver.pop();
			}

			// Get successors for the abstract states (only the successors of
			// the original state
			// have to be checked, but every successor must belong to at least
			// one of the
			// refined states --> assertion)
			solver.push();
			solver.add(PathUtils.unfold(sts.getTrans(), 0));
			for (final ComponentAbstractState succ : as.getSuccessors()) {
				if (stopHandler.isStopped())
					return null;
				if (succ.equals(as))
					continue;
				solver.push();
				SolverHelper.unrollAndAssert(solver, succ.getLabels(), sts, 1);
				boolean isSuccessor = false;
				for (final ComponentAbstractState refined : refinedStates) {
					solver.push();
					SolverHelper.unrollAndAssert(solver, refined.getLabels(), sts, 0);
					if (SolverHelper.checkSat(solver)) {
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
				if (stopHandler.isStopped())
					return null;
				solver.push();
				SolverHelper.unrollAndAssert(solver, ref0.getLabels(), sts, 0);
				for (final ComponentAbstractState ref1 : refinedStates) {
					solver.push();
					SolverHelper.unrollAndAssert(solver, ref1.getLabels(), sts, 1);
					if (SolverHelper.checkSat(solver))
						ref0.getSuccessors().add(ref1);
					solver.pop();
				}

				solver.pop();
			}

			// TODO: store predecessor states
			// Update other states' successors: if the original state was a
			// successor, then remove it
			// and check which refined states are successors (at least one must
			// be --> assertion)
			for (final ComponentAbstractState prev : ks.getStates()) {
				if (stopHandler.isStopped())
					return null;
				if (prev.getSuccessors().contains(as)) {
					boolean isSuccessor = false;
					prev.getSuccessors().remove(as);
					solver.push();
					SolverHelper.unrollAndAssert(solver, prev.getLabels(), sts, 0);
					for (final ComponentAbstractState refined : refinedStates) {
						solver.push();
						SolverHelper.unrollAndAssert(solver, refined.getLabels(), sts, 1);
						if (SolverHelper.checkSat(solver)) {
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

	private List<Valuation> getDeadEndStates(final List<ClusteredAbstractState> abstractCounterEx,
			final int traceLength, final STS sts) {
		final Solver solver = solvers.getSolver();

		final List<Valuation> deadEndStates = new ArrayList<>();
		solver.push();
		solver.add(PathUtils.unfold(sts.getInit(), 0)); // Assert initial
														// conditions
		for (int i = 0; i < traceLength; ++i) {
			for (final ComponentAbstractState as : abstractCounterEx.get(i).getStates())
				for (final Expr<BoolType> label : as.getLabels())
					solver.add(PathUtils.unfold(label, i)); // Labels
			if (i > 0)
				solver.add(PathUtils.unfold(sts.getTrans(), i - 1)); // Transition
																		// relation
		}

		do {
			if (SolverHelper.checkSat(solver)) {
				// Get dead-end state
				final Valuation ds = StsUtils.getConcreteState(solver.getModel(), traceLength - 1, sts.getVars());
				logger.write("Dead end state: ", 6, 1);
				logger.writeln(ds, 6, 0);
				deadEndStates.add(ds);

				// Exclude this state in order to get new dead end states
				solver.add(PathUtils.unfold(Not(ds.toExpr()), traceLength - 1));
			} else
				break;
		} while (true);

		solver.pop();
		return deadEndStates;
	}

	@SuppressWarnings("unused")
	private List<Valuation> getBadStates(final List<ClusteredAbstractState> abstractCounterEx, final int traceLength,
			final STS sts) {
		final Solver solver = solvers.getSolver();

		final List<Valuation> badStates = new ArrayList<>();
		solver.push();
		// Failure state
		for (final ComponentAbstractState as : abstractCounterEx.get(traceLength - 1).getStates())
			for (final Expr<BoolType> label : as.getLabels())
				solver.add(PathUtils.unfold(label, 0)); // Labels
		// Next state
		for (final ComponentAbstractState as : abstractCounterEx.get(traceLength).getStates())
			for (final Expr<BoolType> label : as.getLabels())
				solver.add(PathUtils.unfold(label, 1)); // Labels
		solver.add(PathUtils.unfold(sts.getTrans(), 0)); // Transition relation

		do {
			if (SolverHelper.checkSat(solver)) {
				// Get bad state
				final Valuation bs = StsUtils.getConcreteState(solver.getModel(), 0, sts.getVars());
				logger.write("Bad state: ", 6, 1);
				logger.writeln(bs, 6, 0);
				badStates.add(bs);

				// Exclude this state in order to get new dead end states
				solver.add(PathUtils.unfold(Not(bs.toExpr()), 0));
			} else
				break;
		} while (true);
		solver.pop();
		return badStates;
	}

	private List<Valuation> getConcreteStatesOfAbstractState(final ComponentAbstractState abstractState,
			final STS sts) {
		final Solver solver = solvers.getSolver();

		final List<Valuation> concreteStates = new ArrayList<>();
		solver.push();
		// Assert the labels of the state
		for (final Expr<BoolType> label : abstractState.getLabels())
			solver.add(PathUtils.unfold(label, 0));
		do {
			if (SolverHelper.checkSat(solver)) {
				// Get the model and project
				final Valuation cs = StsUtils.getConcreteState(solver.getModel(), 0,
						abstractState.getCluster().getVars());

				concreteStates.add(cs);
				// Exclude this state to get new ones
				solver.add(PathUtils.unfold(Not(cs.toExpr()), 0));
				logger.write("Concrete state: ", 7, 3);
				logger.writeln(cs, 7, 0);
			} else
				break;
		} while (true);
		solver.pop();
		return concreteStates;
	}

	private boolean checkPair(final ComponentAbstractState as, final Valuation cs0, final Valuation cs1,
			final List<Valuation> deadEndStates, final Set<VarDecl<?>> otherVars, final Solver solver, final STS sts) {

		// Project the dead-end states and check if they are equal
		final List<Valuation> proj0 = projectDeadEndStates(as, cs0, deadEndStates, otherVars, solver, sts);
		final List<Valuation> proj1 = projectDeadEndStates(as, cs1, deadEndStates, otherVars, solver, sts);
		if (proj0.size() != proj1.size())
			return false;

		for (final Valuation p0 : proj0) {
			boolean found = false;
			for (final Valuation p1 : proj1) {
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

	private List<Valuation> projectDeadEndStates(final ComponentAbstractState as, final Valuation cs,
			final List<Valuation> deadEndStates, final Set<VarDecl<?>> otherVars, final Solver solver, final STS sts) {

		// Example: concrete state: (x=1,y=2)
		// The dead-end states are: (x=1,y=2,z=3), (x=1,y=3,z=2), (x=1,y=2,z=5)
		// The result is: (z=3), (z=5)

		final List<Valuation> ret = new ArrayList<>();
		solver.push();
		solver.add(PathUtils.unfold(cs.toExpr(), 0));
		for (final Valuation ds : deadEndStates) {
			solver.push();
			solver.add(PathUtils.unfold(ds.toExpr(), 0));
			if (SolverHelper.checkSat(solver))
				ret.add(StsUtils.getConcreteState(solver.getModel(), 0, otherVars));
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
