package hu.bme.mit.theta.solver.solververifying;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;

import static com.google.common.base.Preconditions.checkState;

public final class VerifyingSolverFactory implements SolverFactory {
	private final String solverName;

	private VerifyingSolverFactory(String solverName) {
		checkState(!solverName.equals("verify")); // no recursive verifier solvers
		this.solverName = solverName;
	}

	public static VerifyingSolverFactory getInstance(String solverName) {
		return new VerifyingSolverFactory(solverName);
	}

	@Override
	public Solver createSolver() {
		try {
			return new VerifyingSolver(solverName);

		} catch (Exception e) {
		e.printStackTrace();
		throw new UnsupportedOperationException("Verifying solver could not be created");
		}
	}

	@Override
	public UCSolver createUCSolver() {
		try {
			return new VerifyingUcSolver(solverName);
		} catch (Exception e) {
			e.printStackTrace();
			throw new UnsupportedOperationException("Verifying UCSolver could not be created");
		}
	}

	@Override
	public ItpSolver createItpSolver() {
		try {
			return new VerifyingItpSolver(solverName);
		} catch (Exception e) {
			e.printStackTrace();
			throw new UnsupportedOperationException("Verifying ITPSolver could not be created");
		}
	}
}
