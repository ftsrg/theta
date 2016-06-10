package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;

import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public final class MutableTCFA implements TCFA {

	private final Collection<TCFALoc> locs;
	private final Collection<TCFAEdge> edges;

	private TCFALoc initLoc;

	public MutableTCFA() {
		locs = new LinkedList<>();
		edges = new LinkedList<>();
		initLoc = createLoc("init");
	}

	////

	@Override
	public TCFALoc getInitLoc() {
		return initLoc;
	}

	public void setInitLoc(final TCFALoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////

	@Override
	public Collection<? extends TCFALoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	public TCFALoc createLoc(final String name) {
		checkNotNull(name);
		final MutableTCFALoc loc = new MutableTCFALoc(name);
		locs.add(loc);
		return loc;
	}

	public void removeLoc(final TCFALoc loc) {
		checkNotNull(loc);
		checkArgument(locs.contains(loc));
		checkArgument(loc != initLoc);
		checkArgument(loc.getInEdges().isEmpty());
		checkArgument(loc.getOutEdges().isEmpty());
		locs.remove(loc);
	}

	////

	@Override
	public Collection<? extends TCFAEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public TCFAEdge createEdge(final TCFALoc source, final TCFALoc target) {
		checkNotNull(source);
		checkNotNull(target);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));

		final MutableTCFALoc mutableSource = (MutableTCFALoc) source;
		final MutableTCFALoc mutableTarget = (MutableTCFALoc) target;

		final MutableTCFAEdge edge = new MutableTCFAEdge(mutableSource, mutableTarget);
		mutableSource.outEdges.add(edge);
		mutableTarget.inEdges.add(edge);
		edges.add(edge);
		return edge;
	}

	public void removeEdge(final TCFAEdge edge) {
		checkNotNull(edge);
		checkArgument(edges.contains(edge));

		final MutableTCFAEdge mutableEdge = (MutableTCFAEdge) edge;

		final MutableTCFALoc source = mutableEdge.source;
		final MutableTCFALoc target = mutableEdge.target;

		source.outEdges.remove(edge);
		target.inEdges.remove(edge);
		edges.remove(edge);
	}

}
