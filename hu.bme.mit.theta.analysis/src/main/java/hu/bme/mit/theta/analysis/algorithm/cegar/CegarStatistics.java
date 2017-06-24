package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.algorithm.Statistics;

/**
 * Represents statistics collected by the CegarChecker algorithm.
 */
public final class CegarStatistics extends Statistics {
	private final long elapsedMillis;
	private final int iterations;

	public CegarStatistics(final long elapsedMillis, final int iterations) {
		this.elapsedMillis = elapsedMillis;
		this.iterations = iterations;

		addStat("ElapsedMillis", this::getElapsedMillis);
		addStat("Iterations", this::getIterations);
	}

	public long getElapsedMillis() {
		return elapsedMillis;
	}

	public int getIterations() {
		return iterations;
	}

}
