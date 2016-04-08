package hu.bme.mit.inf.ttmc.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.common.Loc;

public final class LocState<L extends Loc<L, ?>> implements State<LocState<L>> {

	private static final int HASH_SEED = 8191;

	private final L loc;

	private volatile int hashCode;

	private LocState(final L loc) {
		this.loc = checkNotNull(loc);
	}

	public static <L extends Loc<L, ?>> LocState<L> create(final L loc) {
		return new LocState<>(loc);
	}

	public L getLoc() {
		return loc;
	}

	@Override
	public LocState<L> join(final LocState<L> state) {
		throw new UnsupportedOperationException("join not supported for location states");
	}

	@Override
	public boolean isLeq(final LocState<L> state) {
		return equals(state);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + loc.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof LocState<?>) {
			final LocState<?> that = (LocState<?>) obj;
			return this.loc.equals(that.loc);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("LocState");
		sb.append("(");
		sb.append(loc.toString());
		sb.append(")");
		return sb.toString();
	}

}
