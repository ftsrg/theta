package hu.bme.mit.inf.ttmc.analysis.tcfa.network;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toSet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public final class TCFANetworkLoc implements TCFALoc {

	private final List<TCFALoc> locs;

	private TCFANetworkLoc(final List<? extends TCFALoc> locs) {
		this.locs = ImmutableList.copyOf(checkNotNull(locs));
	}

	public static TCFANetworkLoc create(final List<? extends TCFALoc> locs) {
		return new TCFANetworkLoc(locs);
	}

	////

	public List<TCFALoc> getLocs() {
		return locs;
	}

	@Override
	public Collection<? extends TCFAEdge> getInEdges() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<TCFANetworkEdge> getOutEdges() {
		final Collection<TCFANetworkEdge> networkOutEdges = new ArrayList<>();

		for (int index = 0; index < locs.size(); index++) {
			final TCFALoc loc = locs.get(index);

			for (final TCFAEdge outEdge : loc.getOutEdges()) {
				final List<TCFALoc> outLocs = replace(locs, index, outEdge.getTarget());
				networkOutEdges.add(new TCFANetworkEdge(this, index, outEdge, create(outLocs)));
			}
		}

		return networkOutEdges;
	}

	private static List<TCFALoc> replace(final List<TCFALoc> locs, final int index, final TCFALoc target) {
		final List<TCFALoc> succLocs;

		if (locs.get(index) == target) {
			succLocs = locs;
		} else {
			final TCFALoc[] locArray = locs.toArray(new TCFALoc[0]);
			locArray[index] = target;
			succLocs = ImmutableList.copyOf(locArray);
		}

		return succLocs;

	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isUrgent() {
		return locs.stream().anyMatch(TCFALoc::isUrgent);
	}

	@Override
	public Collection<Expr<? extends BoolType>> getInvars() {
		return locs.stream().map(TCFALoc::getInvars).flatMap(Collection::stream).collect(toSet());
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
		} else if (obj instanceof TCFANetworkLoc) {
			final TCFANetworkLoc that = (TCFANetworkLoc) obj;
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
