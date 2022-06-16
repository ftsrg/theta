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
package hu.bme.mit.theta.xta.analysis.lazy;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.util.concurrent.TimeUnit.MILLISECONDS;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.common.table.TableWriter;

public final class LazyXtaStatistics extends Statistics {

	private final long algorithmTimeInMs;
	private final long expandTimeInMs;
	private final long closeTimeInMs;
	private final long expandExplRefinementTimeInMs;
	private final long expandZoneRefinementTimeInMs;
	private final long closeExplRefinementTimeInMs;
	private final long closeZoneRefinementTimeInMs;
	private final long coverageChecks;
	private final long coverageAttempts;
	private final long coverageSuccesses;
	private final long explRefinementSteps;
	private final long zoneRefinementSteps;
	private final long argDepth;
	private final long argNodes;
	private final long argNodesExpanded;

	private LazyXtaStatistics(final Builder builder) {
		algorithmTimeInMs = builder.algorithmTimer.elapsed(MILLISECONDS);
		expandTimeInMs = builder.expandTimer.elapsed(MILLISECONDS);
		closeTimeInMs = builder.closeTimer.elapsed(MILLISECONDS);
		expandExplRefinementTimeInMs = builder.expandExplRefinementTimer.elapsed(MILLISECONDS);
		expandZoneRefinementTimeInMs = builder.expandZoneRefinementTimer.elapsed(MILLISECONDS);
		closeExplRefinementTimeInMs = builder.closeExplRefinementTimer.elapsed(MILLISECONDS);
		closeZoneRefinementTimeInMs = builder.closeZoneRefinementTimer.elapsed(MILLISECONDS);
		coverageChecks = builder.coverageChecks;
		coverageAttempts = builder.coverageAttempts;
		coverageSuccesses = builder.coverageSuccesses;
		explRefinementSteps = builder.explRefinementSteps;
		zoneRefinementSteps = builder.zoneRefinementSteps;
		argDepth = builder.arg.getDepth();
		argNodes = builder.arg.size();
		argNodesExpanded = builder.arg.getNodes().filter(n -> !n.isSubsumed()).count();

		addStat("AlgorithmTimeInMs", this::getAlgorithmTimeInMs);
		addStat("ExpandTimeInMs", this::getExpandTimeInMs);
		addStat("CloseTimeInMs", this::getCloseTimeInMs);
		addStat("ExpandExplRefinementTimeInMs", this::getExpandExplRefinementTimeInMs);
		addStat("ExpandZoneRefinementTimeInMs", this::getExpandZoneRefinementTimeInMs);
		addStat("CloseExplRefinementTimeInMs", this::getCloseExplRefinementTimeInMs);
		addStat("CloseZoneRefinementTimeInMs", this::getCloseZoneRefinementTimeInMs);
		addStat("CoverageChecks", this::getCoverageChecks);
		addStat("CoverageAttempts", this::getCoverageAttempts);
		addStat("CoverageSuccesses", this::getCoverageSuccesses);
		addStat("ExplRefinementSteps", this::getExplRefinementSteps);
		addStat("ZoneRefinementSteps", this::getZoneRefinementSteps);
		addStat("ArgDepth", this::getArgDepth);
		addStat("ArgNodes", this::getArgNodes);
		addStat("ArgNodesExpanded", this::getArgNodesExpanded);
	}

	public static Builder builder(final ARG<?, ?> arg) {
		return new Builder(arg);
	}

	public long getAlgorithmTimeInMs() {
		return algorithmTimeInMs;
	}

	public long getExpandTimeInMs() {
		return expandTimeInMs;
	}

	public long getCloseTimeInMs() {
		return closeTimeInMs;
	}

	public long getExpandExplRefinementTimeInMs() {
		return expandExplRefinementTimeInMs;
	}

	public long getExpandZoneRefinementTimeInMs() {
		return expandZoneRefinementTimeInMs;
	}

	public long getCloseExplRefinementTimeInMs() {
		return closeExplRefinementTimeInMs;
	}

	public long getCloseZoneRefinementTimeInMs() {
		return closeZoneRefinementTimeInMs;
	}

	public long getCoverageChecks() {
		return coverageChecks;
	}

	public long getCoverageAttempts() {
		return coverageAttempts;
	}

	public long getCoverageSuccesses() {
		return coverageSuccesses;
	}

	public long getExplRefinementSteps() {
		return explRefinementSteps;
	}

	public long getZoneRefinementSteps() {
		return zoneRefinementSteps;
	}

	public long getArgDepth() {
		return argDepth;
	}

	public long getArgNodes() {
		return argNodes;
	}

	public long getArgNodesExpanded() {
		return argNodesExpanded;
	}

	public static void writeHeader(final TableWriter writer) {
		writer.cell("AlgorithmTimeInMs");
		writer.cell("ExpandTimeInMs");
		writer.cell("CloseTimeInMs");
		writer.cell("ExpandExplRefinementTimeInMs");
		writer.cell("ExpandZoneRefinementTimeInMs");
		writer.cell("CloseExplRefinementTimeInMs");
		writer.cell("CloseZoneRefinementTimeInMs");
		writer.cell("CoverageChecks");
		writer.cell("CoverageAttempts");
		writer.cell("CoverageSuccesses");
		writer.cell("ExplRefinementSteps");
		writer.cell("ZoneRefinementSteps");
		writer.cell("ArgDepth");
		writer.cell("ArgNodes");
		writer.cell("ArgNodesExpanded");
		writer.newRow();
	}

	public void writeData(final TableWriter writer) {
		writer.cell(algorithmTimeInMs);
		writer.cell(expandTimeInMs);
		writer.cell(closeTimeInMs);
		writer.cell(expandExplRefinementTimeInMs);
		writer.cell(expandZoneRefinementTimeInMs);
		writer.cell(closeExplRefinementTimeInMs);
		writer.cell(closeZoneRefinementTimeInMs);
		writer.cell(coverageChecks);
		writer.cell(coverageAttempts);
		writer.cell(coverageSuccesses);
		writer.cell(explRefinementSteps);
		writer.cell(zoneRefinementSteps);
		writer.cell(argDepth);
		writer.cell(argNodes);
		writer.cell(argNodesExpanded);
		writer.newRow();
	}

	public static final class Builder {

		private enum State {
			CREATED, RUNNING, EXPANDING, CLOSING, EXPAND_EXPL_REFINING, EXPAND_ZONE_REFINING, CLOSE_EXPL_REFINING, CLOSE_ZONE_REFINING, STOPPED, BUILT
		}

		private State state;

		private final ARG<?, ?> arg;
		private final Stopwatch algorithmTimer;
		private final Stopwatch expandTimer;
		private final Stopwatch closeTimer;
		private final Stopwatch expandExplRefinementTimer;
		private final Stopwatch expandZoneRefinementTimer;
		private final Stopwatch closeExplRefinementTimer;
		private final Stopwatch closeZoneRefinementTimer;
		private long coverageChecks;
		private long coverageAttempts;
		private long coverageSuccesses;
		private long explRefinementSteps;
		private long zoneRefinementSteps;

		private Builder(final ARG<?, ?> arg) {
			this.arg = checkNotNull(arg);
			state = State.CREATED;
			algorithmTimer = Stopwatch.createUnstarted();
			expandTimer = Stopwatch.createUnstarted();
			closeTimer = Stopwatch.createUnstarted();
			expandExplRefinementTimer = Stopwatch.createUnstarted();
			expandZoneRefinementTimer = Stopwatch.createUnstarted();
			closeExplRefinementTimer = Stopwatch.createUnstarted();
			closeZoneRefinementTimer = Stopwatch.createUnstarted();
			coverageChecks = 0;
			coverageAttempts = 0;
			coverageSuccesses = 0;
			explRefinementSteps = 0;
			zoneRefinementSteps = 0;
		}

		public void startAlgorithm() {
			checkState(state == State.CREATED);
			algorithmTimer.start();
			state = State.RUNNING;
		}

		public void stopAlgorithm() {
			checkState(state == State.RUNNING);
			algorithmTimer.stop();
			state = State.STOPPED;
		}

		public void startExpanding() {
			checkState(state == State.RUNNING);
			expandTimer.start();
			state = State.EXPANDING;
		}

		public void stopExpanding() {
			checkState(state == State.EXPANDING);
			expandTimer.stop();
			state = State.RUNNING;
		}

		public void startExpandExplRefinement() {
			checkState(state == State.EXPANDING);
			expandExplRefinementTimer.start();
			state = State.EXPAND_EXPL_REFINING;
		}

		public void stopExpandExplRefinement() {
			checkState(state == State.EXPAND_EXPL_REFINING);
			expandExplRefinementTimer.stop();
			state = State.EXPANDING;
		}

		public void startExpandZoneRefinement() {
			checkState(state == State.EXPANDING);
			expandZoneRefinementTimer.start();
			state = State.EXPAND_ZONE_REFINING;
		}

		public void stopExpandZoneRefinement() {
			checkState(state == State.EXPAND_ZONE_REFINING);
			expandZoneRefinementTimer.stop();
			state = State.EXPANDING;
		}

		public void startClosing() {
			checkState(state == State.RUNNING);
			closeTimer.start();
			state = State.CLOSING;
		}

		public void stopClosing() {
			checkState(state == State.CLOSING);
			closeTimer.stop();
			state = State.RUNNING;
		}

		public void startCloseExplRefinement() {
			checkState(state == State.CLOSING);
			closeExplRefinementTimer.start();
			state = State.CLOSE_EXPL_REFINING;
		}

		public void stopCloseExplRefinement() {
			checkState(state == State.CLOSE_EXPL_REFINING);
			closeExplRefinementTimer.stop();
			state = State.CLOSING;
		}

		public void startCloseZoneRefinement() {
			checkState(state == State.CLOSING);
			closeZoneRefinementTimer.start();
			state = State.CLOSE_ZONE_REFINING;
		}

		public void stopCloseZoneRefinement() {
			checkState(state == State.CLOSE_ZONE_REFINING);
			closeZoneRefinementTimer.stop();
			state = State.CLOSING;
		}

		public void checkCoverage() {
			checkState(state == State.CLOSING);
			coverageChecks++;
		}

		public void attemptCoverage() {
			checkState(state == State.CLOSING);
			coverageAttempts++;
		}

		public void successfulCoverage() {
			checkState(state == State.CLOSING);
			coverageSuccesses++;
		}

		public void refineExpl() {
			checkState(state == State.EXPAND_EXPL_REFINING || state == State.CLOSE_EXPL_REFINING);
			explRefinementSteps++;
		}

		public void refineZone() {
			checkState(state == State.EXPAND_ZONE_REFINING || state == State.CLOSE_ZONE_REFINING);
			zoneRefinementSteps++;
		}

		public LazyXtaStatistics build() {
			checkState(state == State.STOPPED);
			state = State.BUILT;
			return new LazyXtaStatistics(this);
		}

	}
}
