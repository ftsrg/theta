/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.algorithm.Statistics;

/**
 * Represents statistics collected by the CegarChecker algorithm.
 */
public final class CegarStatistics extends Statistics {
	private final long algorithmTimeMs;
	private final long abstractorTimeMs;
	private final long refinerTimeMs;
	private final int iterations;

	public CegarStatistics(final long algorithmTimeMs, final long abstractorTimeMs, final long refinerTimeMs,
			final int iterations) {
		this.algorithmTimeMs = algorithmTimeMs;
		this.abstractorTimeMs = abstractorTimeMs;
		this.refinerTimeMs = refinerTimeMs;
		this.iterations = iterations;

		addStat("AlgorithmTimeMs", this::getAlgorithmTimeMs);
		addStat("Iterations", this::getIterations);
	}

	public long getAlgorithmTimeMs() {
		return algorithmTimeMs;
	}

	public long getAbstractorTimeMs() {
		return abstractorTimeMs;
	}

	public long getRefinerTimeMs() {
		return refinerTimeMs;
	}

	public int getIterations() {
		return iterations;
	}

}
