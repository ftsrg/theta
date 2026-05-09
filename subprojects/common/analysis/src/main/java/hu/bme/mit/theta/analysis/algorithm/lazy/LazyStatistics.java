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
package hu.bme.mit.theta.analysis.algorithm.lazy;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.common.table.TableWriter;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.util.concurrent.TimeUnit.MILLISECONDS;

public final class LazyStatistics extends Statistics {

	private final long algorithmTimeInMs;
	private final long expandTimeInMs;
	private final long closeTimeInMs;
	private final long expandState1RefinementTimeInMs;
	private final long expandState2RefinementTimeInMs;
	private final long closeState1RefinementTimeInMs;
	private final long closeState2RefinementTimeInMs;
	private final long coverageChecks;
	private final long coverageAttempts;
	private final long coverageSuccesses;
	private final long state1RefinementSteps;
	private final long state2RefinementSteps;
	private final long argDepth;
	private final long argNodes;
	private final long argNodesExpanded;

	private LazyStatistics(final Builder builder) {
		algorithmTimeInMs = builder.algorithmTimer.elapsed(MILLISECONDS);
		expandTimeInMs = builder.expandTimer.elapsed(MILLISECONDS);
		closeTimeInMs = builder.closeTimer.elapsed(MILLISECONDS);
		expandState1RefinementTimeInMs = builder.expandState1RefinementTimer.elapsed(MILLISECONDS);
		expandState2RefinementTimeInMs = builder.expandState2RefinementTimer.elapsed(MILLISECONDS);
		closeState1RefinementTimeInMs = builder.closeState1RefinementTimer.elapsed(MILLISECONDS);
		closeState2RefinementTimeInMs = builder.closeState2RefinementTimer.elapsed(MILLISECONDS);
		coverageChecks = builder.coverageChecks;
		coverageAttempts = builder.coverageAttempts;
		coverageSuccesses = builder.coverageSuccesses;
		state1RefinementSteps = builder.state1RefinementSteps;
		state2RefinementSteps = builder.state2RefinementSteps;
		argDepth = builder.arg.getDepth();
		argNodes = builder.arg.size();
		argNodesExpanded = builder.arg.getNodes().filter(n -> !n.isSubsumed()).count();

		addStat("AlgorithmTimeInMs", this::getAlgorithmTimeInMs);
		addStat("ExpandTimeInMs", this::getExpandTimeInMs);
		addStat("CloseTimeInMs", this::getCloseTimeInMs);
		addStat("ExpandState1RefinementTimeInMs", this::getExpandState1RefinementTimeInMs);
		addStat("ExpandState2RefinementTimeInMs", this::getExpandState2RefinementTimeInMs);
		addStat("CloseState1RefinementTimeInMs", this::getCloseState1RefinementTimeInMs);
		addStat("CloseState2RefinementTimeInMs", this::getCloseState2RefinementTimeInMs);
		addStat("CoverageChecks", this::getCoverageChecks);
		addStat("CoverageAttempts", this::getCoverageAttempts);
		addStat("CoverageSuccesses", this::getCoverageSuccesses);
		addStat("State1RefinementSteps", this::getState1RefinementSteps);
		addStat("State2RefinementSteps", this::getState2RefinementSteps);
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

	public long getExpandState1RefinementTimeInMs() {
		return expandState1RefinementTimeInMs;
	}

	public long getExpandState2RefinementTimeInMs() {
		return expandState2RefinementTimeInMs;
	}

	public long getCloseState1RefinementTimeInMs() {
		return closeState1RefinementTimeInMs;
	}

	public long getCloseState2RefinementTimeInMs() {
		return closeState2RefinementTimeInMs;
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

	public long getState1RefinementSteps() {
		return state1RefinementSteps;
	}

	public long getState2RefinementSteps() {
		return state2RefinementSteps;
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
		writer.cell("ExpandState1RefinementTimeInMs");
		writer.cell("ExpandState2RefinementTimeInMs");
		writer.cell("CloseState1RefinementTimeInMs");
		writer.cell("CloseState2RefinementTimeInMs");
		writer.cell("CoverageChecks");
		writer.cell("CoverageAttempts");
		writer.cell("CoverageSuccesses");
		writer.cell("State1RefinementSteps");
		writer.cell("State2RefinementSteps");
		writer.cell("ArgDepth");
		writer.cell("ArgNodes");
		writer.cell("ArgNodesExpanded");
		writer.newRow();
	}

	public void writeData(final TableWriter writer) {
		writer.cell(algorithmTimeInMs);
		writer.cell(expandTimeInMs);
		writer.cell(closeTimeInMs);
		writer.cell(expandState1RefinementTimeInMs);
		writer.cell(expandState2RefinementTimeInMs);
		writer.cell(closeState1RefinementTimeInMs);
		writer.cell(closeState2RefinementTimeInMs);
		writer.cell(coverageChecks);
		writer.cell(coverageAttempts);
		writer.cell(coverageSuccesses);
		writer.cell(state1RefinementSteps);
		writer.cell(state2RefinementSteps);
		writer.cell(argDepth);
		writer.cell(argNodes);
		writer.cell(argNodesExpanded);
		writer.newRow();
	}

	public static class Builder {

    private enum AlgorithmState {
			CREATED, RUNNING, EXPANDING, CLOSING, EXPAND_STATE_1_REFINING, EXPAND_STATE_2_REFINING, CLOSE_STATE_1_REFINING, CLOSE_STATE_2_REFINING, STOPPED, BUILT
		}

    private enum BuilderState {
      STATE_1, STATE_2
    }

    private AlgorithmState algorithmState;
    private BuilderState builderState;

    private final ARG<?, ?> arg;
    private final Stopwatch algorithmTimer;
    private final Stopwatch expandTimer;
    private final Stopwatch closeTimer;
    private final Stopwatch expandState1RefinementTimer;
    private final Stopwatch expandState2RefinementTimer;
    private final Stopwatch closeState1RefinementTimer;
    private final Stopwatch closeState2RefinementTimer;
    private long coverageChecks;
    private long coverageAttempts;
    private long coverageSuccesses;
    private long state1RefinementSteps;
    private long state2RefinementSteps;

		private Builder(final ARG<?, ?> arg) {
			this.arg = checkNotNull(arg);
			algorithmState = AlgorithmState.CREATED;
      builderState = BuilderState.STATE_1;
			algorithmTimer = Stopwatch.createUnstarted();
			expandTimer = Stopwatch.createUnstarted();
			closeTimer = Stopwatch.createUnstarted();
			expandState1RefinementTimer = Stopwatch.createUnstarted();
			expandState2RefinementTimer = Stopwatch.createUnstarted();
			closeState1RefinementTimer = Stopwatch.createUnstarted();
			closeState2RefinementTimer = Stopwatch.createUnstarted();
			coverageChecks = 0;
			coverageAttempts = 0;
			coverageSuccesses = 0;
			state1RefinementSteps = 0;
			state2RefinementSteps = 0;
		}

		public void startAlgorithm() {
			checkState(algorithmState == AlgorithmState.CREATED);
			algorithmTimer.start();
			algorithmState = AlgorithmState.RUNNING;
		}

		public void stopAlgorithm() {
			checkState(algorithmState == AlgorithmState.RUNNING);
			algorithmTimer.stop();
			algorithmState = AlgorithmState.STOPPED;
		}

		public void startExpanding() {
			checkState(algorithmState == AlgorithmState.RUNNING);
			expandTimer.start();
			algorithmState = AlgorithmState.EXPANDING;
		}

		public void stopExpanding() {
			checkState(algorithmState == AlgorithmState.EXPANDING);
			expandTimer.stop();
			algorithmState = AlgorithmState.RUNNING;
		}

    public void startExpandRefinement() {
      if (builderState == BuilderState.STATE_1) {
        startExpandState1Refinement();
      } else {
        startExpandState2Refinement();
      }
    }

    public void stopExpandRefinement() {
      if (builderState == BuilderState.STATE_1) {
        stopExpandState1Refinement();
      } else {
        stopExpandState2Refinement();
      }
    }

		private void startExpandState1Refinement() {
			checkState(algorithmState == AlgorithmState.EXPANDING);
			expandState1RefinementTimer.start();
			algorithmState = AlgorithmState.EXPAND_STATE_1_REFINING;
		}

		private void stopExpandState1Refinement() {
			checkState(algorithmState == AlgorithmState.EXPAND_STATE_1_REFINING);
			expandState1RefinementTimer.stop();
			algorithmState = AlgorithmState.EXPANDING;
		}

		private void startExpandState2Refinement() {
			checkState(algorithmState == AlgorithmState.EXPANDING);
			expandState2RefinementTimer.start();
			algorithmState = AlgorithmState.EXPAND_STATE_2_REFINING;
		}

		private void stopExpandState2Refinement() {
			checkState(algorithmState == AlgorithmState.EXPAND_STATE_2_REFINING);
			expandState2RefinementTimer.stop();
			algorithmState = AlgorithmState.EXPANDING;
		}

		public void startClosing() {
			checkState(algorithmState == AlgorithmState.RUNNING);
			closeTimer.start();
			algorithmState = AlgorithmState.CLOSING;
		}

		public void stopClosing() {
			checkState(algorithmState == AlgorithmState.CLOSING);
			closeTimer.stop();
			algorithmState = AlgorithmState.RUNNING;
		}

    public void startCloseRefinement() {
      if (builderState == BuilderState.STATE_1) {
        startCloseState1Refinement();
      } else {
        startCloseState2Refinement();
      }
    }

    public void stopCloseRefinement() {
      if (builderState == BuilderState.STATE_1) {
        stopCloseState1Refinement();
      } else {
        stopCloseState2Refinement();
      }
    }

		private void startCloseState1Refinement() {
			checkState(algorithmState == AlgorithmState.CLOSING);
			closeState1RefinementTimer.start();
			algorithmState = AlgorithmState.CLOSE_STATE_1_REFINING;
		}

		private void stopCloseState1Refinement() {
			checkState(algorithmState == AlgorithmState.CLOSE_STATE_1_REFINING);
			closeState1RefinementTimer.stop();
			algorithmState = AlgorithmState.CLOSING;
		}

		private void startCloseState2Refinement() {
			checkState(algorithmState == AlgorithmState.CLOSING);
			closeState2RefinementTimer.start();
			algorithmState = AlgorithmState.CLOSE_STATE_2_REFINING;
		}

		private void stopCloseState2Refinement() {
			checkState(algorithmState == AlgorithmState.CLOSE_STATE_2_REFINING);
			closeState2RefinementTimer.stop();
			algorithmState = AlgorithmState.CLOSING;
		}

		public void checkCoverage() {
			checkState(algorithmState == AlgorithmState.CLOSING);
			coverageChecks++;
		}

		public void attemptCoverage() {
			checkState(algorithmState == AlgorithmState.CLOSING);
			coverageAttempts++;
		}

		public void successfulCoverage() {
			checkState(algorithmState == AlgorithmState.CLOSING);
			coverageSuccesses++;
		}

    public void refine() {
      if (builderState == BuilderState.STATE_1) {
        refineState1();
      } else {
        refineState2();
      }
    }

		private void refineState1() {
			checkState(algorithmState == AlgorithmState.EXPAND_STATE_1_REFINING || algorithmState == AlgorithmState.CLOSE_STATE_1_REFINING);
			state1RefinementSteps++;
		}

		private void refineState2() {
			checkState(algorithmState == AlgorithmState.EXPAND_STATE_2_REFINING || algorithmState == AlgorithmState.CLOSE_STATE_2_REFINING);
			state2RefinementSteps++;
		}

    public void setState1() {
      builderState = BuilderState.STATE_1;
    }

    public void setState2() {
      builderState = BuilderState.STATE_2;
    }

    public void clearState() {
      builderState = BuilderState.STATE_1;
    }

		public LazyStatistics build() {
			checkState(algorithmState == AlgorithmState.STOPPED);
			algorithmState = AlgorithmState.BUILT;
			return new LazyStatistics(this);
		}
	}
}
