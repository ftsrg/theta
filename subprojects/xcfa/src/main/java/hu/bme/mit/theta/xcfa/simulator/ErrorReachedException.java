package hu.bme.mit.theta.xcfa.simulator;

/** Reached error location or deadlock */
public class ErrorReachedException extends Exception {

	public ErrorReachedException(String message) {
		super(message);
	}
}
