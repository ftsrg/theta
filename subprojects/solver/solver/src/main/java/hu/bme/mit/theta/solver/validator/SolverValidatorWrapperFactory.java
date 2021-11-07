package hu.bme.mit.theta.solver.validator;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;

import static com.google.common.base.Preconditions.checkState;

public final class SolverValidatorWrapperFactory implements SolverFactory {
	private final String solverName;

	private SolverValidatorWrapperFactory(String solverName) {
		this.solverName = solverName;
	}

	public static SolverValidatorWrapperFactory create(String solverName) {
		return new SolverValidatorWrapperFactory(solverName);
	}

	@Override
	public Solver createSolver() {
		try {
			return new SolverValidatorWrapper(solverName);

		} catch (Exception e) {
		e.printStackTrace();
		throw new UnsupportedOperationException("Verifying solver could not be created");
		}
	}

	@Override
	public UCSolver createUCSolver() {
		try {
			return new UCSolverValidatorWrapper(solverName);
		} catch (Exception e) {
			e.printStackTrace();
			throw new UnsupportedOperationException("Verifying UCSolver could not be created");
		}
	}

	@Override
	public ItpSolver createItpSolver() {
		try {
			return new ItpSolverValidatorWrapper(solverName);
		} catch (Exception e) {
			e.printStackTrace();
			throw new UnsupportedOperationException("Verifying ITPSolver could not be created");
		}
	}
}
