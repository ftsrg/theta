package hu.bme.mit.theta.analysis.xta.algorithm.itp;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.Statistics;

public final class XtaItpStatistics implements Statistics {

	private final long algorithmTimeInMs;
	private final long refinementTimeInMs;
	private final long interpolationTimeInMs;
	private final long refinementSteps;
	private final long argDepth;
	private final long argNodes;
	private final long argNodesExpanded;

	private XtaItpStatistics(final Builder builder) {
		algorithmTimeInMs = builder.algorithmTimer.elapsed(TimeUnit.MILLISECONDS);
		refinementTimeInMs = builder.refinementTimer.elapsed(TimeUnit.MILLISECONDS);
		interpolationTimeInMs = builder.interpolationTimer.elapsed(TimeUnit.MILLISECONDS);
		refinementSteps = builder.refinementSteps;
		argDepth = builder.arg.getDepth();
		argNodes = builder.arg.getNodes().count();
		argNodesExpanded = builder.arg.getNodes().filter(ArgNode::isExpanded).count();
	}

	public static Builder builder(final ARG<?, ?> arg) {
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

	public long getArgNodesExpanded() {
		return argNodesExpanded;
	}

	public static final class Builder {

		private static enum State {
			CREATED, RUNNING, REFINING, INTERPOLATING, STOPPED, BUILT
		}

		private State state;

		private final ARG<?, ?> arg;
		private final Stopwatch algorithmTimer;
		private final Stopwatch refinementTimer;
		private final Stopwatch interpolationTimer;

		private long refinementSteps;

		private Builder(final ARG<?, ?> arg) {
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

		public XtaItpStatistics build() {
			checkState(state == State.STOPPED);
			state = State.BUILT;
			return new XtaItpStatistics(this);
		}

	}

}
