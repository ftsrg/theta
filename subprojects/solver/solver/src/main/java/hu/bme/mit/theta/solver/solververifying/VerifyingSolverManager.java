package hu.bme.mit.theta.solver.solververifying;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverBase;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.UCSolver;

import java.util.HashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class VerifyingSolverManager extends SolverManager {
	private static final String NAME = "verify";

	private boolean closed = false;
	private String verifiedSolverName;
	private final Set<SolverBase> instantiatedSolvers = new HashSet<>();

	private VerifyingSolverManager(String verifiedSolverName) {
		this.verifiedSolverName = verifiedSolverName;
	}

	public static VerifyingSolverManager create(String verifiedSolverName) {
		return new VerifyingSolverManager(verifiedSolverName);
	}

	@Override
	public boolean managesSolver(String name) {
		return name.equals("verify");
	}

	@Override
	public SolverFactory getSolverFactory(String name) throws Exception {
		checkArgument(NAME.equals(name));
		return new ManagedFactory(VerifyingSolverFactory.getInstance(verifiedSolverName));
	}

	@Override
	public void close() throws Exception {
		for(final var solver : instantiatedSolvers) {
			solver.close();
		}
		closed = true;
	}

	private final class ManagedFactory implements SolverFactory {
		private final SolverFactory solverFactory;

		private ManagedFactory(final SolverFactory solverFactory) {
			this.solverFactory = solverFactory;
		}

		@Override
		public Solver createSolver() {
			checkState(!closed, "Solver manager was closed");
			final var solver = solverFactory.createSolver();
			instantiatedSolvers.add(solver);
			return solver;
		}

		@Override
		public UCSolver createUCSolver() {
			checkState(!closed, "Solver manager was closed");
			final var solver = solverFactory.createUCSolver();
			instantiatedSolvers.add(solver);
			return solver;
		}

		@Override
		public ItpSolver createItpSolver() {
			checkState(!closed, "Solver manager was closed");
			final var solver = solverFactory.createItpSolver();
			instantiatedSolvers.add(solver);
			return solver;
		}
	}
}
