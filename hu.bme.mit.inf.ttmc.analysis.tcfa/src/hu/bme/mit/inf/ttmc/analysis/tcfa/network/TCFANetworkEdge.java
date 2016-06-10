package hu.bme.mit.inf.ttmc.analysis.tcfa.network;

import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;

public final class TCFANetworkEdge implements TCFAEdge {

	private final TCFANetworkLoc source;
	private final TCFANetworkLoc target;
	private final int index;
	private final TCFAEdge edge;

	TCFANetworkEdge(final TCFANetworkLoc source, final int index, final TCFAEdge edge, final TCFANetworkLoc target) {
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
	public TCFANetworkLoc getSource() {
		return source;
	}

	@Override
	public TCFANetworkLoc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return edge.getStmts();
	}

	////

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof TCFANetworkEdge) {
			final TCFANetworkEdge that = (TCFANetworkEdge) obj;
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
