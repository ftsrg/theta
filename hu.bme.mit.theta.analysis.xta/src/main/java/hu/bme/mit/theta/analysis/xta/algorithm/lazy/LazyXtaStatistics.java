package hu.bme.mit.theta.analysis.xta.algorithm.lazy;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.util.stream.Collectors.toSet;

import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.common.Tuple;

public final class LazyXtaStatistics implements Statistics {

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
				.map(n -> Tuple.of(n.getState().getLocs(), n.getState().getVal())).collect(toSet()).size();
	}

	public static Builder builder(final ARG<? extends XtaState<?>, ?> arg) {
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

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("algorithmTimeInMs = " + algorithmTimeInMs + "\n");
		sb.append("refinementTimeInMs = " + refinementTimeInMs + "\n");
		sb.append("interpolationTimeInMs = " + interpolationTimeInMs + "\n");
		sb.append("refinementSteps = " + refinementSteps + "\n");
		sb.append("argDepth = " + argDepth + "\n");
		sb.append("argNodes = " + argNodes + "\n");
		sb.append("argNodesFeasible = " + argNodesFeasible + "\n");
		sb.append("argNodesExpanded = " + argNodesExpanded + "\n");
		sb.append("discreteStatesExpanded = " + discreteStatesExpanded + "\n");
		return sb.toString();
	}

	public static final class Builder {

		private static enum State {
			CREATED, RUNNING, REFINING, INTERPOLATING, STOPPED, BUILT
		}

		private State state;

		private final ARG<? extends XtaState<?>, ?> arg;
		private final Stopwatch algorithmTimer;
		private final Stopwatch refinementTimer;
		private final Stopwatch interpolationTimer;

		private long refinementSteps;

		private Builder(final ARG<? extends XtaState<?>, ?> arg) {
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
