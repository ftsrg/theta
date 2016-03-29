package hu.bme.mit.inf.ttmc.formalism.cfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public class MutableCFA implements CFA {

	private CFALoc initLoc;
	private CFALoc finalLoc;
	private CFALoc errorLoc;

	private final Collection<CFALoc> locs;
	private final Collection<CFAEdge> edges;

	public MutableCFA() {
		locs = new HashSet<>();
		edges = new HashSet<>();

		initLoc = new MutableCFALoc();
		finalLoc = new MutableCFALoc();
		errorLoc = new MutableCFALoc();

		locs.add(initLoc);
		locs.add(finalLoc);
		locs.add(errorLoc);
	}

	////

	@Override
	public CFALoc getInitLoc() {
		return initLoc;
	}

	public void setInitLoc(final CFALoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////

	@Override
	public CFALoc getFinalLoc() {
		return finalLoc;
	}

	public void setFinalLoc(final CFALoc finalLoc) {
		checkNotNull(finalLoc);
		checkArgument(locs.contains(finalLoc));
		this.finalLoc = finalLoc;
	}

	////

	@Override
	public CFALoc getErrorLoc() {
		return errorLoc;
	}

	public void setErrorLoc(final CFALoc errorLoc) {
		checkNotNull(errorLoc);
		checkArgument(locs.contains(errorLoc));
		this.errorLoc = errorLoc;
	}

	////

	@Override
	public Collection<CFALoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	public MutableCFALoc createLoc() {
		final MutableCFALoc loc = new MutableCFALoc();
		locs.add(loc);
		return loc;
	}

	public void removeLoc(final CFALoc loc) {
		checkNotNull(loc);
		checkArgument(locs.contains(loc));
		checkArgument(loc != initLoc);
		checkArgument(loc != finalLoc);
		checkArgument(loc != errorLoc);
		checkArgument(loc.getInEdges().isEmpty());
		checkArgument(loc.getOutEdges().isEmpty());
		locs.remove(loc);
	}

	////

	@Override
	public Collection<CFAEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public MutableCFAEdge createEdge(final CFALoc source, final CFALoc target) {
		checkNotNull(source);
		checkNotNull(target);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));
		
		final MutableCFALoc mutableSource = (MutableCFALoc) source;
		final MutableCFALoc mutableTarget = (MutableCFALoc) target;

		final MutableCFAEdge edge = new MutableCFAEdge(mutableSource, mutableTarget);
		mutableSource.addOutEdge(edge);
		mutableTarget.addOutEdge(edge);
		edges.add(edge);
		return edge;
	}

	public void removeEdge(final CFAEdge edge) {
		checkNotNull(edge);
		checkArgument(edges.contains(edge));

		final CFALoc source = edge.getSource();
		final CFALoc target = edge.getTarget();

		checkNotNull(source);
		checkNotNull(target);

		final MutableCFALoc mutableSource = (MutableCFALoc) source;
		final MutableCFALoc mutableTarget = (MutableCFALoc) target;

		mutableSource.removeOutEdge(edge);
		mutableTarget.removeInEdge(edge);
		edges.remove(edge);
	}

}
