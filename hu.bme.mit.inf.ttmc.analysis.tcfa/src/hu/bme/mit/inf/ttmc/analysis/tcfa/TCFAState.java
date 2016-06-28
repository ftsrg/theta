package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public final class TCFAState<S extends State> implements State {

	private static final int HASH_SEED = 3613;

	private volatile int hashCode = 0;

	private final TCFALoc loc;
	private final S state;

	private TCFAState(final TCFALoc loc, final S state) {
		this.loc = checkNotNull(loc);
		this.state = checkNotNull(state);
	}

	public static <S extends State> TCFAState<S> create(final TCFALoc loc, final S state) {
		return new TCFAState<>(loc, state);
	}

	////

	public S getState() {
		return state;
	}

	public TCFALoc getLoc() {
		return loc;
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
		} else if (obj instanceof TCFAState) {
			final TCFAState<?> that = (TCFAState<?>) obj;
			return this.loc.equals(that.loc) && this.state.equals(that.state);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("TCFAState(");
		sb.append(loc);
		sb.append(", ");
		sb.append(state);
		sb.append(")");
		return sb.toString();
	}

}
