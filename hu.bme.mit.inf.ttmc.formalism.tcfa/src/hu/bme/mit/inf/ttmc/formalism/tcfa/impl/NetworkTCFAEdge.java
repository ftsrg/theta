package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;

final class NetworkTCFAEdge implements TCFAEdge {

	private static final int HASH_SEED = 9161;

	private volatile int hashCode;

	private final NetworkTCFALoc source;
	private final NetworkTCFALoc target;
	private final int index;
	private final TCFAEdge edge;

	NetworkTCFAEdge(final NetworkTCFALoc source, final int index, final TCFAEdge edge, final NetworkTCFALoc target) {
		this.source = source;
		this.edge = edge;
		this.index = index;
		this.target = target;
	}

	public int getIndex() {
		return index;
	}

	public TCFAEdge getEdge() {
		return edge;
	}

	@Override
	public NetworkTCFALoc getSource() {
		return source;
	}

	@Override
	public NetworkTCFALoc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return edge.getStmts();
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + source.hashCode();
			result = 31 * result + target.hashCode();
			result = 31 * result + index;
			result = 31 * result + edge.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof NetworkTCFAEdge) {
			final NetworkTCFAEdge that = (NetworkTCFAEdge) obj;
			return this.index == that.index && this.source.equals(that.source) && this.target.equals(that.target)
					&& this.edge.equals(that.edge);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
