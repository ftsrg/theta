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
package hu.bme.mit.theta.formalism.xta.analysis.lazy;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.util.stream.Collectors.toSet;

import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;

public final class LazyXtaStatistics extends Statistics {

	private final long algorithmTimeInMs;
	private final long refinementTimeInMs;
	private final long interpolationTimeInMs;
	private final long refinementSteps;
	private final long argDepth;
	private final long argNodes;
	private final long argNodesFeasible;
	private final long argNodesExpanded;
	private final long discreteStatesExpanded;

	private LazyXtaStatistics(final Builder builder) {
		algorithmTimeInMs = builder.algorithmTimer.elapsed(TimeUnit.MILLISECONDS);
		refinementTimeInMs = builder.refinementTimer.elapsed(TimeUnit.MILLISECONDS);
		interpolationTimeInMs = builder.interpolationTimer.elapsed(TimeUnit.MILLISECONDS);
		refinementSteps = builder.refinementSteps;
		argDepth = builder.arg.getDepth();
		argNodes = builder.arg.getNodes().count();
		argNodesFeasible = builder.arg.getNodes().filter(ArgNode::isFeasible).count();
		argNodesExpanded = builder.arg.getNodes().filter(ArgNode::isExpanded).count();
		discreteStatesExpanded = builder.arg.getNodes().filter(ArgNode::isExpanded)
				.map(n -> Tuple2.of(n.getState().getLocs(), n.getState().getState()._1())).collect(toSet()).size();

		addStat("AlgorithmTimeInMs", this::getAlgorithmTimeInMs);
		addStat("RefinementTimeInMs", this::getRefinementTimeInMs);
		addStat("InterpolationTimeInMs", this::getInterpolationTimeInMs);
		addStat("RefinementSteps", this::getRefinementSteps);
		addStat("ArgDepth", this::getArgDepth);
		addStat("ArgNodes", this::getArgNodes);
		addStat("ArgNodesFeasible", this::getArgNodesFeasible);
		addStat("ArgNodesExpanded", this::getArgNodesExpanded);
		addStat("DiscreteStatesExpanded", this::getDiscreteStatesExpanded);
	}

	public static Builder builder(final ARG<? extends XtaState<? extends Prod2State<ExplState, ?>>, ?> arg) {
		return new Builder(arg);
	}

	public long getAlgorithmTimeInMs() {
		return algorithmTimeInMs;
	}

	public long getRefinementTimeInMs() {
		return refinementTimeInMs;
	}

	public long getInterpolationTimeInMs() {
		return interpolationTimeInMs;
	}

	public long getRefinementSteps() {
		return refinementSteps;
	}

	public long getArgDepth() {
		return argDepth;
	}

	public long getArgNodes() {
		return argNodes;
	}

	public long getArgNodesFeasible() {
		return argNodesFeasible;
	}

	public long getArgNodesExpanded() {
		return argNodesExpanded;
	}

	public long getDiscreteStatesExpanded() {
		return discreteStatesExpanded;
	}

	public static final class Builder {

		private enum State {
			CREATED, RUNNING, REFINING, INTERPOLATING, STOPPED, BUILT
		}

		private State state;

		private final ARG<? extends XtaState<? extends Prod2State<ExplState, ?>>, ?> arg;
		private final Stopwatch algorithmTimer;
		private final Stopwatch refinementTimer;
		private final Stopwatch interpolationTimer;

		private long refinementSteps;

		private Builder(final ARG<? extends XtaState<? extends Prod2State<ExplState, ?>>, ?> arg) {
			this.arg = checkNotNull(arg);
			state = State.CREATED;
			algorithmTimer = Stopwatch.createUnstarted();
			refinementTimer = Stopwatch.createUnstarted();
			interpolationTimer = Stopwatch.createUnstarted();
			refinementSteps = 0;
		}

		public void startAlgorithm() {
			checkState(state == State.CREATED);
			state = State.RUNNING;
			algorithmTimer.start();
		}

		public void stopAlgorithm() {
			checkState(state == State.RUNNING);
			algorithmTimer.stop();
			state = State.STOPPED;
		}

		public void startRefinement() {
			checkState(state == State.RUNNING);
			state = State.REFINING;
			refinementTimer.start();
		}

		public void stopRefinement() {
			checkState(state == State.REFINING);
			refinementTimer.stop();
			state = State.RUNNING;
		}

		public void startInterpolation() {
			checkState(state == State.REFINING);
			state = State.INTERPOLATING;
			interpolationTimer.start();
		}

		public void stopInterpolation() {
			checkState(state == State.INTERPOLATING);
			interpolationTimer.stop();
			state = State.REFINING;
		}

		public void refine() {
			checkState(state == State.REFINING);
			refinementSteps++;
		}

		public LazyXtaStatistics build() {
			checkState(state == State.STOPPED);
			state = State.BUILT;
			return new LazyXtaStatistics(this);
		}

	}
}
