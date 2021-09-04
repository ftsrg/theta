package hu.bme.mit.theta.analysis.algorithm.cegar;

public interface NotSolvableThrower {
	public void throwNotSolvableException();
	public void throwNoNewCexException();
}
