package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.cegar.common.data.KripkeStructure;
import hu.bme.mit.inf.ttmc.cegar.common.steps.CEGARStepBase;
import hu.bme.mit.inf.ttmc.cegar.common.steps.IInitializer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.FormulaCollector;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.impl.STSCNFTransformation;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.impl.STSITETransformation;

/**
 * Initial abstraction creator step.
 *
 * @author Akos
 */
public class InterpolatingInitializer extends CEGARStepBase implements IInitializer<InterpolatedAbstractSystem> {

	private final boolean collectFromConditions, collectFromSpecification;
	private final boolean useCNFTransformation;
	private final Set<String> explicitVariableNames; // List of explicitly tracked variables

	/**
	 * Initialize the step with a solver, logger, visualizer and collection
	 * parameters
	 *
	 * @param solver
	 * @param logger
	 * @param visualizer
	 * @param collectFromConditions
	 *            Should the initial predicates be collected from the conditions
	 * @param collectFromSpecification
	 *            Should the initial predicates be collected from the
	 *            specification
	 * @param useCNFTransformation
	 *            Should the constraints be transformed into CNF form
	 * @param explicitVariables
	 *            List of explicitly tracked variables
	 */
	public InterpolatingInitializer(final Logger logger, final IVisualizer visualizer, final boolean collectFromConditions,
			final boolean collectFromSpecification, final boolean useCNFTransformation, final Collection<String> explicitVariables) {
		super(logger, visualizer);
		this.collectFromConditions = collectFromConditions;
		this.collectFromSpecification = collectFromSpecification;
		this.useCNFTransformation = useCNFTransformation;
		this.explicitVariableNames = new HashSet<>(explicitVariables);
	}

	@Override
	public InterpolatedAbstractSystem create(STS concrSys) {
		final Solver solver = concrSys.getManager().getSolverFactory().createSolver(true, false);
		logger.writeln("Specification expression: " + concrSys.getProp(), 2);

		final Map<String, VarDecl<? extends Type>> varMap = new HashMap<>();
		final Set<VarDecl<? extends Type>> explicitVars = new HashSet<>();
		// Print variables
		logger.write("Variables [" + concrSys.getVars().size() + "]:", 2);
		for (final VarDecl<? extends Type> varDecl : concrSys.getVars()) {
			logger.write(" " + varDecl.getName(), 3);
			varMap.put(varDecl.getName(), varDecl);
		}
		logger.writeln(2);

		logger.write("Explicitly tracked [" + explicitVariableNames.size() + "]:", 2);
		for (final String varName : explicitVariableNames)
			logger.write(" " + varName, 2);
		logger.writeln(2);

		// Check explicitly tracked variables
		int variablesNotFound = 0; // Count not found variables for assertion
		for (final String varName : explicitVariableNames) {
			if (!varMap.containsKey(varName)) {
				logger.writeln("Warning: variable '" + varName + "' does not exist.", 0);
				++variablesNotFound;
			} else {
				explicitVars.add(varMap.get(varName));
			}
		}

		assert (explicitVariableNames.size() == variablesNotFound + explicitVars.size());

		// Collect initial predicates to a set that ensures uniqueness for isomorphic expressions

		final Set<Expr<? extends BoolType>> initialPredSet = new HashSet<>();

		// Collect atomic formulas from the conditions
		if (collectFromConditions)
			FormulaCollector.collectAtomsFromTransitionConditions(concrSys, initialPredSet);
		// Collect atomic formulas from the specification
		if (collectFromSpecification)
			FormulaCollector.collectAtomsFromExpression(concrSys.getProp(), initialPredSet);

		// If no predicate could be collected start with 'true'
		if (initialPredSet.size() == 0)
			initialPredSet.add(concrSys.getManager().getExprFactory().True());

		// Move the collected predicates to a list for further use
		final List<Expr<? extends BoolType>> initialPredList = new ArrayList<>(initialPredSet);

		// There must be at least one predicate
		assert (initialPredList.size() > 0);

		logger.writeln("Initial predicates [" + initialPredList.size() + "]", 2);
		for (final Expr<? extends BoolType> ex : initialPredList)
			logger.writeln(ex, 3, 1);

		if (isStopped)
			return null;

		// Eliminate if-then-else expressions from the constraints by replacing them with implications
		logger.write("Eliminating if-then-else expressions from the constraints...", 3);
		concrSys = new STSITETransformation().transform(concrSys);
		logger.writeln("done.", 3);

		// Apply CNF transformation if needed
		final List<VarDecl<? extends Type>> cnfVariables = new ArrayList<>();
		final List<VarDecl<? extends Type>> nonCnfVariables = new ArrayList<>(concrSys.getVars());
		if (useCNFTransformation) {
			logger.write("Transforming constraints to CNF...", 3);
			concrSys = new STSCNFTransformation().transform(concrSys);
			for (final VarDecl<? extends Type> varDecl : concrSys.getVars()) {
				if (!nonCnfVariables.contains(varDecl))
					cnfVariables.add(varDecl);
			}
			// # normal variables + # new variables == # all variables
			assert (nonCnfVariables.size() + cnfVariables.size() == concrSys.getVars().size());
			logger.writeln("done, " + cnfVariables.size() + " new variables were added.", 3);
		}

		logger.writeln("### Using new system from now on ###", 0);

		final InterpolatedAbstractSystem system = new InterpolatedAbstractSystem(concrSys);

		system.getVariables().addAll(nonCnfVariables);
		system.getCNFVariables().addAll(cnfVariables);
		system.getExplicitVariables().addAll(explicitVars);

		assert (system.getVariables().size() + system.getCNFVariables().size() == system.getSystem().getVars().size());

		system.getInitialPredicates().addAll(initialPredList);

		// Create the initial abstract Kripke structure based on the initial predicates
		// and explicit variables

		// Calculate negate for each formula
		final List<Expr<? extends BoolType>> negates = new ArrayList<>();
		for (final Expr<? extends BoolType> ex : system.getInitialPredicates())
			negates.add(concrSys.getManager().getExprFactory().Not(ex));

		final STSUnroller unroller = system.getUnroller(); // Create an unroller for k=1

		// Traverse the possible abstract states. Each formula is either unnegated or negated, so
		// there are 2^|formulas| possible abstract states. We start with an empty state (no
		// formulas) and in each step we expand the state with the unnegated and negated version
		// of the next formula, i.e., two new states may be obtained (if feasible).
		final Stack<InterpolatedAbstractState> stack = new Stack<>();
		final List<InterpolatedAbstractState> predicateStates = new ArrayList<>();
		stack.push(new InterpolatedAbstractState()); // Start with no formulas

		solver.push();
		solver.add(unroller.inv(0));

		while (!stack.isEmpty()) {
			if (isStopped)
				return null;
			final InterpolatedAbstractState actual = stack.pop(); // Get the next state

			// Add the next formula unnegated
			final InterpolatedAbstractState s1 = actual.cloneAndAdd(system.getInitialPredicates().get(actual.getLabels().size()));
			if (isStateFeasible(solver, s1, unroller)) {
				// If the state is feasible and there are no more formulas, this state is finished
				if (s1.getLabels().size() == system.getInitialPredicates().size())
					predicateStates.add(s1);
				else
					stack.push(s1);
			}

			// Add the next formula negated
			final InterpolatedAbstractState s2 = actual.cloneAndAdd(negates.get(actual.getLabels().size()));
			if (isStateFeasible(solver, s2, unroller)) {
				// If the state is feasible and there are no more formulas, this state is finished
				if (s2.getLabels().size() == system.getInitialPredicates().size())
					predicateStates.add(s2);
				else
					stack.push(s2);
			}
		}

		final KripkeStructure<InterpolatedAbstractState> ks = new KripkeStructure<>();

		// After predicates are added, explicit variables can also be added
		if (system.getExplicitVariables().size() > 0) {
			// Loop through each state and get explicit variables
			for (final InterpolatedAbstractState as : predicateStates) {
				if (isStopped)
					return null;
				solver.push();
				// Assert labels of the state
				SolverHelper.unrollAndAssert(solver, as.getLabels(), unroller, 0);
				do { // Loop until a new state is found
					if (SolverHelper.checkSatisfiable(solver)) {
						// Keep only explicitly tracked variables
						final AndExpr model = unroller.getConcreteState(solver.getModel(), 0, system.getExplicitVariables());
						ks.addState(as.cloneAndAddExplicit(model));
						solver.add(unroller.unroll(concrSys.getManager().getExprFactory().Not(model), 0)); // Exclude this state
					} else
						break;
				} while (true);
				solver.pop();
			}
		} else {
			for (final InterpolatedAbstractState as : predicateStates)
				ks.addState(as);
		}

		// Calculate initial states and transition relation
		logger.writeln("Abstract states [" + ks.getStates().size() + "]", 2);
		for (final InterpolatedAbstractState s0 : ks.getStates()) { // Loop through the states
			if (isStopped)
				return null;
			s0.setInitial(isStateInitial(solver, s0, unroller)); // Check whether it is initial
			if (s0.isInitial())
				ks.addInitialState(s0);
			for (final InterpolatedAbstractState s1 : ks.getStates()) { // Calculate successors
				if (isStopped)
					return null;
				if (isTransitionFeasible(solver, s0, s1, unroller)) {
					s0.addSuccessor(s1);
					s1.addPredecessor(s0);
				}
			}
			logger.writeln(s0, 4, 1);
		}
		solver.pop();

		system.setAbstractKripkeStructure(ks);

		return system;
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
	private boolean isStateFeasible(final Solver solver, final InterpolatedAbstractState s, final STSUnroller unroller) {
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
	private boolean isStateInitial(final Solver solver, final InterpolatedAbstractState s, final STSUnroller unroller) {
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
	private boolean isTransitionFeasible(final Solver solver, final InterpolatedAbstractState s0, final InterpolatedAbstractState s1,
			final STSUnroller unroller) {
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
		final List<String> tokens = new ArrayList<String>();
		if (collectFromConditions)
			tokens.add("collectFromCond");
		if (collectFromSpecification)
			tokens.add("collectFromSpec");
		if (useCNFTransformation)
			tokens.add("CNF");
		if (explicitVariableNames.size() > 0)
			tokens.add("explicit(" + String.join(",", explicitVariableNames) + ")");
		return String.join(",", tokens);
	}
}
