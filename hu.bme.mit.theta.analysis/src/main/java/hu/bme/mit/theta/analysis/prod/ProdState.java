package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.product.Product;

public abstract class ProdState implements ExprState, Product, Iterable<State> {

	private static final int HASH_SEED = 7573;
	private volatile int hashCode = 0;

	private final List<State> states;

	ProdState(final List<? extends State> states) {
		this.states = ImmutableList.copyOf(checkNotNull(states));
	}

	////

	public static <S1 extends State, S2 extends State> Prod2State<S1, S2> of(final S1 state1, final S2 state2) {
		return new Prod2State<>(state1, state2);
	}

	public static <S1 extends State, S2 extends State, S3 extends State> Prod3State<S1, S2, S3> of(final S1 state1,
			final S2 state2, final S3 state3) {
		return new Prod3State<>(state1, state2, state3);
	}

	////

	public static <S1 extends State, S2 extends State> Collection<Prod2State<S1, S2>> product(
			final Collection<? extends S1> states1, final Collection<? extends S2> states2) {
		checkNotNull(states1);
		checkNotNull(states2);

		final ImmutableCollection.Builder<Prod2State<S1, S2>> builder = ImmutableSet.builder();
		for (final S1 state1 : states1) {
			for (final S2 state2 : states2) {
				builder.add(ProdState.of(state1, state2));
			}
		}
		return builder.build();
	}

	public static <S1 extends State, S2 extends State, S3 extends State> Collection<Prod3State<S1, S2, S3>> product(
			final Collection<? extends S1> states1, final Collection<? extends S2> states2,
			final Collection<? extends S3> states3) {
		checkNotNull(states1);
		checkNotNull(states2);

		final ImmutableCollection.Builder<Prod3State<S1, S2, S3>> builder = ImmutableSet.builder();
		for (final S1 state1 : states1) {
			for (final S2 state2 : states2) {
				for (final S3 state3 : states3) {
					builder.add(ProdState.of(state1, state2, state3));
				}
			}
		}
		return builder.build();
	}

	////

	@Override
	public final int arity() {
		return states.size();
	}

	@Override
	public final Object elem(final int n) {
		checkElementIndex(n, arity());
		return states.get(n);
	}

	@Override
	public final List<State> toList() {
		return states;
	}

	@Override
	public final Iterator<State> iterator() {
		return states.iterator();
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + states.hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ProdState) {
			final ProdState that = (ProdState) obj;
			return this.states.equals(that.states);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(states).toString();
	}

}
