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
import hu.bme.mit.inf.ttmc.cegar.common.data.SolverWrapper;
import hu.bme.mit.inf.ttmc.cegar.common.data.StopHandler;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.steps.Initializer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.FormulaCollector;
import hu.bme.mit.inf.ttmc.cegar.common.utils.SolverHelper;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.impl.STSCNFTransformation;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.impl.STSITETransformation;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class InterpolatingInitializer extends AbstractCEGARStep implements Initializer<InterpolatedAbstractSystem> {

	private final boolean collectFromConditions, collectFromSpecification;
	private final boolean useCNFTransformation;
	private final Set<String> explicitVarNames;

	public InterpolatingInitializer(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger, final Visualizer visualizer,
			final boolean collectFromConditions, final boolean collectFromSpecification, final boolean useCNFTransformation,
			final Collection<String> explicitVariables) {
		super(solvers, stopHandler, logger, visualizer);
		this.collectFromConditions = collectFromConditions;
		this.collectFromSpecification = collectFromSpecification;
		this.useCNFTransformation = useCNFTransformation;
		this.explicitVarNames = new HashSet<>(explicitVariables);
	}

	@Override
	public InterpolatedAbstractSystem create(STS concrSys) {

		final Map<String, VarDecl<? extends Type>> varMap = new HashMap<>();
		final Set<VarDecl<? extends Type>> explicitVars = new HashSet<>();

		logger.write("Variables [" + concrSys.getVars().size() + "]:", 2);
		for (final VarDecl<? extends Type> varDecl : concrSys.getVars()) {
			logger.write(" " + varDecl.getName(), 3);
			varMap.put(varDecl.getName(), varDecl);
		}
		logger.writeln(2);

		logger.write("Explicitly tracked [" + explicitVarNames.size() + "]:", 2);
		for (final String varName : explicitVarNames)
			logger.write(" " + varName, 2);
		logger.writeln(2);

		logger.writeln("Specification expression: " + concrSys.getProp(), 2);

		// Check explicitly tracked variables
		int variablesNotFound = 0; // Count not found variables for assertion
		for (final String varName : explicitVarNames) {
			if (!varMap.containsKey(varName)) {
				logger.writeln("Warning: variable '" + varName + "' does not exist.", 0);
				++variablesNotFound;
			} else {
				explicitVars.add(varMap.get(varName));
			}
		}

		assert (explicitVarNames.size() == variablesNotFound + explicitVars.size());

		// Set ensures uniqueness
		final Set<Expr<? extends BoolType>> initialPredSet = new HashSet<>();
		if (collectFromConditions)
			FormulaCollector.collectAtomsFromTransitionConditions(concrSys, initialPredSet);
		if (collectFromSpecification)
			FormulaCollector.collectAtomsFromExpression(concrSys.getProp(), initialPredSet);

		// If no predicate could be collected start with 'true'
		if (initialPredSet.size() == 0)
			initialPredSet.add(Exprs.True());

		// Move the collected predicates to a list for further use
		final List<Expr<? extends BoolType>> initialPredList = new ArrayList<>(initialPredSet);

		// There must be at least one predicate
		assert (initialPredList.size() > 0);

		logger.writeln("Initial predicates [" + initialPredList.size() + "]", 2);
		for (final Expr<? extends BoolType> ex : initialPredList)
			logger.writeln(ex, 3, 1);

		if (stopHandler.isStopped())
			return null;

		// Eliminate if-then-else expressions from the constraints by replacing
		// them with implications
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

		final InterpolatedAbstractSystem system = new InterpolatedAbstractSystem(concrSys);

		system.getVars().addAll(nonCnfVariables);
		system.getCNFVariables().addAll(cnfVariables);
		system.getExplicitVariables().addAll(explicitVars);

		assert (system.getVars().size() + system.getCNFVariables().size() == system.getSTS().getVars().size());

		system.getInitialPredicates().addAll(initialPredList);

		// Create the initial abstract Kripke structure based on the initial
		// predicates and explicit variables

		// Calculate negate for each formula
		final List<Expr<? extends BoolType>> negates = new ArrayList<>();
		for (final Expr<? extends BoolType> ex : system.getInitialPredicates())
			negates.add(Exprs.Not(ex));

		final STS sts = system.getSTS();

		// Traverse the possible abstract states. Each formula is either
		// unnegated or negated, so
		// there are 2^|formulas| possible abstract states. We start with an
		// empty state (no
		// formulas) and in each step we expand the state with the unnegated and
		// negated version
		// of the next formula, i.e., two new states may be obtained (if
		// feasible).
		final Stack<InterpolatedAbstractState> stack = new Stack<>();
		final List<InterpolatedAbstractState> predicateStates = new ArrayList<>();
		stack.push(new InterpolatedAbstractState()); // Start with no formulas

		final Solver solver = solvers.getSolver();
		solver.push();
		solver.add(sts.unrollInv(0));

		while (!stack.isEmpty()) {
			if (stopHandler.isStopped())
				return null;

			// Get the next state
			final InterpolatedAbstractState actual = stack.pop();

			// Add the next formula unnegated
			final InterpolatedAbstractState s1 = actual.cloneAndAdd(system.getInitialPredicates().get(actual.getLabels().size()));
			if (isStateFeasible(s1, solver, sts)) {
				// If the state is feasible and there are no more formulas, this
				// state is finished
				if (s1.getLabels().size() == system.getInitialPredicates().size())
					predicateStates.add(s1);
				else
					stack.push(s1);
			}

			// Add the next formula negated
			final InterpolatedAbstractState s2 = actual.cloneAndAdd(negates.get(actual.getLabels().size()));
			if (isStateFeasible(s2, solver, sts)) {
				// If the state is feasible and there are no more formulas, this
				// state is finished
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
				if (stopHandler.isStopped())
					return null;
				solver.push();
				// Assert labels of the state
				SolverHelper.unrollAndAssert(solver, as.getLabels(), sts, 0);
				do { // Loop until a new state is found
					if (stopHandler.isStopped())
						return null;
					if (SolverHelper.checkSat(solver)) {
						// Keep only explicitly tracked variables
						final AndExpr model = sts.getConcreteState(solver.getModel(), 0, system.getExplicitVariables());
						ks.addState(as.cloneAndAddExplicit(model));

						// Exclude this state
						solver.add(sts.unroll(Exprs.Not(model), 0));
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

		// Loop through the states
		for (final InterpolatedAbstractState s0 : ks.getStates()) {
			if (stopHandler.isStopped())
				return null;

			// Check whether it is initial
			s0.setInitial(isStateInitial(s0, solver, sts));

			if (s0.isInitial())
				ks.addInitialState(s0);

			// Calculate successors
			for (final InterpolatedAbstractState s1 : ks.getStates()) {

				if (stopHandler.isStopped())
					return null;
				if (isTransitionFeasible(s0, s1, solver, sts)) {
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

	private boolean isStateFeasible(final InterpolatedAbstractState s, final Solver solver, final STS sts) {
		solver.push();
		SolverHelper.unrollAndAssert(solver, s.getLabels(), sts, 0);
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	private boolean isStateInitial(final InterpolatedAbstractState s, final Solver solver, final STS sts) {
		solver.push();
		SolverHelper.unrollAndAssert(solver, s.getLabels(), sts, 0);
		solver.add(sts.unrollInit(0));
		final boolean ret = SolverHelper.checkSat(solver);
		solver.pop();
		return ret;
	}

	private boolean isTransitionFeasible(final InterpolatedAbstractState s0, final InterpolatedAbstractState s1, final Solver solver, final STS sts) {
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
		final List<String> tokens = new ArrayList<String>();
		if (collectFromConditions)
			tokens.add("collectFromCond");
		if (collectFromSpecification)
			tokens.add("collectFromSpec");
		if (useCNFTransformation)
			tokens.add("CNF");
		if (explicitVarNames.size() > 0)
			tokens.add("explicit(" + String.join(",", explicitVarNames) + ")");
		return String.join(",", tokens);
	}
}
