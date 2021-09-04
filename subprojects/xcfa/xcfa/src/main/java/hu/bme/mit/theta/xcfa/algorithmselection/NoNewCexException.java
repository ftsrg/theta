package hu.bme.mit.theta.xcfa.algorithmselection;

public class NotSolvableException extends RuntimeException {
	NotSolvableException() {
		super("Task is not solvable with this configuration!");
	}
}