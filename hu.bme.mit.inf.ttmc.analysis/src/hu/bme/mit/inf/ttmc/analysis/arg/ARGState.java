package hu.bme.mit.inf.ttmc.analysis.arg;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.State;

public class ARGState<S extends State> implements State {
	private final S state;

	private final Optional<ARGState<S>> parent;
	private final Set<ARGState<S>> successors;
	private Optional<Boolean> isTarget;

	private ARGState(final S state, final ARGState<S> parent) {
		this.state = checkNotNull(state);
		this.parent = parent != null ? Optional.of(parent) : Optional.empty();
		isTarget = Optional.empty();
		successors = new HashSet<>();
	}

	public static <S extends State> ARGState<S> create(final S state, final ARGState<S> parent) {
		return new ARGState<>(state, parent);
	}

	public static <S extends State> ARGState<S> create(final S state) {
		return new ARGState<>(state, null);
	}

	public S getState() {
		return state;
	}

	public boolean isStart() {
		return !parent.isPresent();
	}

	public Optional<Boolean> isTarget() {
		return isTarget;
	}

	public void setTarget(final boolean isTarget) {
		this.isTarget = Optional.of(isTarget);
	}

	public void addSuccessor(final ARGState<S> state) {
		this.successors.add(state);
	}

	public Collection<? extends ARGState<S>> getSuccessors() {
		return Collections.unmodifiableSet(successors);
	}

	public Optional<ARGState<S>> getParent() {
		return parent;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("ArgState(");
		sb.append(state.toString());
		if (isStart()) {
			sb.append(", start");
		}
		if (isTarget.isPresent() && isTarget.get()) {
			sb.append(", target");
		}
		sb.append(')');
		return sb.toString();
	}
}
