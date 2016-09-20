package hu.bme.mit.theta.formalism.tcfa.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toSet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class NetworkTcfaLoc implements TcfaLoc {

	private static final int HASH_SEED = 2543;

	private final List<TcfaLoc> locs;

	private volatile int hashCode = 0;

	NetworkTcfaLoc(final List<? extends TcfaLoc> locs) {
		this.locs = ImmutableList.copyOf(checkNotNull(locs));
	}

	////

	public List<TcfaLoc> getLocs() {
		return locs;
	}

	@Override
	public Collection<? extends TcfaEdge> getInEdges() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<NetworkTcfaEdge> getOutEdges() {
		final Collection<NetworkTcfaEdge> networkOutEdges = new ArrayList<>();

		for (int index = 0; index < locs.size(); index++) {
			final TcfaLoc loc = locs.get(index);

			for (final TcfaEdge outEdge : loc.getOutEdges()) {
				final List<TcfaLoc> outLocs = replace(locs, index, outEdge.getTarget());
				networkOutEdges.add(new NetworkTcfaEdge(this, index, outEdge, new NetworkTcfaLoc(outLocs)));
			}
		}

		return networkOutEdges;
	}

	private static List<TcfaLoc> replace(final List<TcfaLoc> locs, final int index, final TcfaLoc target) {
		final List<TcfaLoc> succLocs;

		if (locs.get(index) == target) {
			succLocs = locs;
		} else {
			final TcfaLoc[] locArray = locs.toArray(new TcfaLoc[0]);
			locArray[index] = target;
			succLocs = ImmutableList.copyOf(locArray);
		}

		return succLocs;
	}

	@Override
	public String getName() {
		final StringJoiner joiner = new StringJoiner("_");
		locs.forEach(l -> joiner.add(l.getName()));
		return joiner.toString();
	}

	@Override
	public boolean isUrgent() {
		return locs.stream().anyMatch(TcfaLoc::isUrgent);
	}

	@Override
	public Collection<Expr<? extends BoolType>> getInvars() {
		return locs.stream().map(TcfaLoc::getInvars).flatMap(Collection::stream).collect(toSet());
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + locs.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof NetworkTcfaLoc) {
			final NetworkTcfaLoc that = (NetworkTcfaLoc) obj;
			return this.locs.equals(that.locs);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "TCFALoc(", ")");
		locs.stream().forEach(l -> sj.add(l.getName()));
		return sj.toString();
	}

}
