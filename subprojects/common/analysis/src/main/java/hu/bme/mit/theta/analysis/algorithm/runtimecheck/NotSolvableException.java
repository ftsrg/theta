package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

public class NotSolvableException extends RuntimeException {
	NotSolvableException() {
		super("Task is not solvable with this configuration!");
	}
}