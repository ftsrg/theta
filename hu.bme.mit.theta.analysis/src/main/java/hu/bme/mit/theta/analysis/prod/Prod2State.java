package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkPositionIndex;

import java.util.Collection;

import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.Product2;

public final class Prod2State<S1 extends State, S2 extends State> implements State, Product2<S1, S2> {

	private static final int HASH_SEED = 7573;

	private volatile int hashCode = 0;

	private final S1 state1;
	private final S2 state2;

	private Prod2State(final S1 state1, final S2 state2) {
		this.state1 = checkNotNull(state1);
		this.state2 = checkNotNull(state2);
	}

	public static <S1 extends State, S2 extends State> Prod2State<S1, S2> of(final S1 state1, final S2 state2) {
		return new Prod2State<>(state1, state2);
	}

	public static <S1 extends State, S2 extends State> Collection<Prod2State<S1, S2>> product(
			final Collection<? extends S1> states1, final Collection<? extends S2> states2) {
		checkNotNull(states1);
		checkNotNull(states2);

		final ImmutableCollection.Builder<Prod2State<S1, S2>> builder = ImmutableSet.builder();
		for (final S1 state1 : states1) {
			for (final S2 state2 : states2) {
				builder.add(Prod2State.of(state1, state2));
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

	////

	public <S extends State> Prod2State<S, S2> with1(final S state) {
		return Prod2State.of(state, this.state2);
	}

	public <S extends State> Prod2State<S1, S> with2(final S state) {
		return Prod2State.of(this.state1, state);
	}

	////

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
		} else if (obj instanceof Prod2State<?, ?>) {
			final Prod2State<?, ?> that = (Prod2State<?, ?>) obj;
			return this.state1.equals(that.state1) && this.state2.equals(that.state2);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(state1).add(state2).toString();
	}

}
