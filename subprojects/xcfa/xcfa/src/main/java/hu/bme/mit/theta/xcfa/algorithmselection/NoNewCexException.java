package hu.bme.mit.theta.xcfa.algorithmselection;

public class NoNewCexException extends RuntimeException {
	NoNewCexException() {
		super("There was no new abstract counterexample found in task!");
	}
}