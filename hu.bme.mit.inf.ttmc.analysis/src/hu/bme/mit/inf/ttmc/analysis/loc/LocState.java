package hu.bme.mit.inf.ttmc.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;

public final class LocState implements State {
	
	private final CFALoc loc;
	
	private volatile int hashCode = 0;
	
	public LocState(final CFALoc loc) {
		this.loc = checkNotNull(loc);
	}
	
	public CFALoc getLoc() {
		return loc;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = 659;
			hashCode = 31 * hashCode + loc.hashCode();
		}

		return hashCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final LocState that = (LocState) obj;
			return this.loc.equals(that.loc);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("LocState (");
		sb.append(loc);
		sb.append(")");
		return sb.toString();
	}
	
}
