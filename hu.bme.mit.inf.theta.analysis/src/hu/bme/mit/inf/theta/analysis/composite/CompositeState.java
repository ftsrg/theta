package hu.bme.mit.inf.theta.analysis.composite;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkPositionIndex;

import java.util.Collection;

import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.theta.analysis.State;
import hu.bme.mit.inf.theta.common.Product2;

public final class CompositeState<S1 extends State, S2 extends State> implements State, Product2<S1, S2> {

	private static final int HASH_SEED = 7573;

	private volatile int hashCode = 0;

	private final S1 state1;
	private final S2 state2;

	private CompositeState(final S1 state1, final S2 state2) {
		this.state1 = checkNotNull(state1);
		this.state2 = checkNotNull(state2);
	}

	public static <S1 extends State, S2 extends State> CompositeState<S1, S2> create(final S1 state1, final S2 state2) {
		return new CompositeState<>(state1, state2);
	}

	public static <S1 extends State, S2 extends State> Collection<CompositeState<S1, S2>> product(
			final Collection<? extends S1> states1, final Collection<? extends S2> states2) {
		checkNotNull(states1);
		checkNotNull(states2);

		final ImmutableCollection.Builder<CompositeState<S1, S2>> builder = ImmutableSet.builder();
		for (final S1 state1 : states1) {
			for (final S2 state2 : states2) {
				builder.add(create(state1, state2));
			}
		}
		return builder.build();
	}

	@Override
	public S1 _1() {
		return state1;
	}

	@Override
	public S2 _2() {
		return state2;
	}

	@Override
	public int arity() {
		return 2;
	}

	@Override
	public State elem(final int n) {
		checkPositionIndex(n, 2);
		return n == 0 ? _1() : _2();
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + state1.hashCode();
			result = 37 * result + state2.hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof CompositeState<?, ?>) {
			final CompositeState<?, ?> that = (CompositeState<?, ?>) obj;
			return this.state1.equals(that.state1) && this.state2.equals(that.state2);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("CompositeState");
		sb.append("(");
		sb.append(state1);
		sb.append(", ");
		sb.append(state2);
		sb.append(")");
		return sb.toString();
	}

}
