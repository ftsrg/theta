package hu.bme.mit.theta.solver;

public enum SolverStatus {
	SAT, UNSAT, UNKNOWN;

	public boolean boolValue() {
		if (this == SAT)
			return true;
		else if (this == UNSAT)
			return false;
		else
			throw new UnknownSolverStatusException();
	}
}
