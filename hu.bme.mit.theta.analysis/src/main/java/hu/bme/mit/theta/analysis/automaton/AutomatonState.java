package hu.bme.mit.theta.analysis.automaton;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class AutomatonState<S extends State, L extends Loc<L, E>, E extends Edge<L, E>> implements State {

	private static final int HASH_SEED = 3613;

	private volatile int hashCode = 0;

	private final L loc;
	private final S state;

	private AutomatonState(final L loc, final S state) {
		this.loc = checkNotNull(loc);
		this.state = checkNotNull(state);
	}

	public static <S extends State, L extends Loc<L, E>, E extends Edge<L, E>> AutomatonState<S, L, E> create(
			final L loc, final S state) {
		return new AutomatonState<>(loc, state);
	}

	////

	public L getLoc() {
		return loc;
	}

	public S getState() {
		return state;
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + loc.hashCode();
			result = 31 * result + state.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AutomatonState) {
			final AutomatonState<?, ?, ?> that = (AutomatonState<?, ?, ?>) obj;
			return this.loc.equals(that.loc) && this.state.equals(that.state);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("AutomatonState(");
		sb.append(loc);
		sb.append(", ");
		sb.append(state);
		sb.append(")");
		return sb.toString();
	}

}
