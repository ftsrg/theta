package hu.bme.mit.theta.solver;

public enum SolverStatus {
	SAT(true), UNSAT(false);

	private final boolean sat;

	private SolverStatus(final boolean sat) {
		this.sat = sat;
	}

	public boolean isSat() {
		return sat;
	}

	public boolean isUnsat() {
		return !sat;
	}

}
