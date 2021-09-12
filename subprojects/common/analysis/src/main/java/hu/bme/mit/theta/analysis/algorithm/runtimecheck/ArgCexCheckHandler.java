package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

public class ArgCexCheckHandler {
	public static ArgCexCheckHandler instance = new ArgCexCheckHandler();
	private boolean shouldCheck = false;

	public void setArgCexCheck(boolean shouldThrow) {
		this.shouldCheck = shouldThrow;
	}

	public boolean shouldCheck() {
		return shouldCheck;
	}

	public void throwNotSolvableException() {
		if(shouldCheck) {
			System.err.println("Not solvable!");
			throw new NotSolvableException();
		}
	}
}
