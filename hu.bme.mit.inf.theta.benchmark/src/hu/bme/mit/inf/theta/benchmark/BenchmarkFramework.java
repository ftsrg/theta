package hu.bme.mit.inf.theta.benchmark;

import java.util.ArrayList;
import java.util.List;

public class BenchmarkFramework {

	private static class MeasureResult {
		public int id;
		public String filename;

		public int cfaLocCount;
		public int depth;

		public MeasureResult(int id) {
			this.id = id;
		}
	}

	private final List<BenchmarkConfiguration> configs = new ArrayList<>();

	public void addConfig(BenchmarkConfiguration config) {
		this.configs.add(config);
	}

	/**
	 * Theoratical measurement
	 */
	public void measure() {

	}

}
