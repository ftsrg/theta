package hu.bme.mit.theta.xcfa.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.cegar.NotSolvableThrower;

public class PortfolioNotSolvableThrower implements NotSolvableThrower {
	private boolean shouldThrow = false;

	public PortfolioNotSolvableThrower(boolean shouldThrow) {
		this.shouldThrow = shouldThrow;
	}

	@Override
	public void throwNotSolvableException() {
		if(shouldThrow) {
			System.err.println("Not solvable!");
			throw new NotSolvableException();
		}
	}

	@Override
	public void throwNoNewCexException() {
		if(shouldThrow) {
			System.err.println("Not solvable!");
			throw new NoNewCexException();
		}
	}
}
