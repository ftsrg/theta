package hu.bme.mit.inf.ttmc.constraint.z3.factory;

import com.microsoft.z3.InterpolationContext;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.z3.solver.Z3ItpSolver;
import hu.bme.mit.inf.ttmc.constraint.z3.solver.Z3Solver;
import hu.bme.mit.inf.ttmc.constraint.z3.solver.Z3TermWrapper;

public final class Z3SolverFactory implements SolverFactory {

	final ConstraintManager manager;
	final InterpolationContext context;
	final Z3TermWrapper termWrapper;
	
	public Z3SolverFactory(final ConstraintManager manager, final InterpolationContext context, final Z3TermWrapper termWrapper) {
		this.manager = manager;
		this.context = context;
		this.termWrapper = termWrapper;
	}

	@Override
	public Solver createSolver(final boolean genModels, final boolean genUnsatCores) {
		return new Z3Solver(manager, context, termWrapper);
	}

	@Override
	public ItpSolver createItpSolver() {
		return new Z3ItpSolver(manager, context, termWrapper);
	}

}
