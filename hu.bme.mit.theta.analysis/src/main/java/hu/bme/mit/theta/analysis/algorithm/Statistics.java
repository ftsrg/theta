package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.common.ObjectUtils;

public class Statistics {
	private final long elapsedMillis;
	private final int iterations;

	public Statistics(final long elapsedMillis, final int iterations) {
		this.elapsedMillis = elapsedMillis;
		this.iterations = iterations;
	}

	public long getElapsedMillis() {
		return elapsedMillis;
	}

	public int getIterations() {
		return iterations;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add("Iterations: " + iterations)
				.add("Elapsed: " + elapsedMillis + " ms").toString();
	}
}
