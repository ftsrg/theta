package hu.bme.mit.inf.ttmc.analysis.arg;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.State;

public class ArgState<S extends State> implements State {
	private final S state;

	private final Optional<ArgState<S>> parent;
	private final Set<ArgState<S>> successors;
	private Optional<Boolean> isStart;
	private Optional<Boolean> isTarget;

	private ArgState(final S state, final ArgState<S> parent) {
		this.state = checkNotNull(state);
		this.parent = parent != null ? Optional.of(parent) : Optional.empty();
		isStart = Optional.empty();
		isTarget = Optional.empty();
		successors = new HashSet<>();
	}

	public static <S extends State> ArgState<S> create(final S state, final ArgState<S> parent) {
		return new ArgState<>(state, parent);
	}

	public static <S extends State> ArgState<S> create(final S state) {
		return new ArgState<>(state, null);
	}

	public S getState() {
		return state;
	}

	public Optional<Boolean> isStart() {
		return isStart;
	}

	public void setStart(final boolean isStart) {
		this.isStart = Optional.of(isStart);
	}

	public Optional<Boolean> isTarget() {
		return isTarget;
	}

	public void setTarget(final boolean isTarget) {
		this.isTarget = Optional.of(isTarget);
	}

	public void addSuccessor(final ArgState<S> state) {
		this.successors.add(state);
	}

	public Collection<? extends ArgState<S>> getSuccessors() {
		return Collections.unmodifiableSet(successors);
	}

	public Optional<ArgState<S>> getParent() {
		return parent;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("ArgState(");
		sb.append(state.toString());
		if (isStart.isPresent() && isStart.get()) {
			sb.append(", start");
		}
		if (isTarget.isPresent() && isTarget.get()) {
			sb.append(", target");
		}
		sb.append(')');
		return sb.toString();
	}
}
