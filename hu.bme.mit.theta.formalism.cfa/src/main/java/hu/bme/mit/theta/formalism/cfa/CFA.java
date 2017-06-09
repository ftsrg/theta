package hu.bme.mit.theta.formalism.cfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.theta.formalism.common.Automaton;

public final class CFA implements Automaton<CfaLoc, CfaEdge> {
	private int nextId;

	private CfaLoc initLoc;
	private CfaLoc finalLoc;
	private CfaLoc errorLoc;

	private final Collection<CfaLoc> locs;
	private final Collection<CfaEdge> edges;

	public CFA() {
		locs = new HashSet<>();
		edges = new HashSet<>();
		initLoc = createLoc();
		finalLoc = createLoc();
		errorLoc = createLoc();
		nextId = 0;
	}

	////

	@Override
	public CfaLoc getInitLoc() {
		return initLoc;
	}

	public void setInitLoc(final CfaLoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////

	public CfaLoc getFinalLoc() {
		return finalLoc;
	}

	public void setFinalLoc(final CfaLoc finalLoc) {
		checkNotNull(finalLoc);
		checkArgument(locs.contains(finalLoc));
		this.finalLoc = finalLoc;
	}

	////

	public CfaLoc getErrorLoc() {
		return errorLoc;
	}

	public void setErrorLoc(final CfaLoc errorLoc) {
		checkNotNull(errorLoc);
		checkArgument(locs.contains(errorLoc));
		this.errorLoc = errorLoc;
	}

	////

	@Override
	public Collection<CfaLoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	public CfaLoc createLoc() {
		final CfaLoc loc = new CfaLoc(nextId + "");
		++nextId;
		locs.add(loc);
		return loc;
	}

	public void removeLoc(final CfaLoc loc) {
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
	public Collection<CfaEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public CfaEdge createEdge(final CfaLoc source, final CfaLoc target) {
		checkNotNull(source);
		checkNotNull(target);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));

		final CfaLoc mutableSource = source;
		final CfaLoc mutableTarget = target;

		final CfaEdge edge = new CfaEdge(mutableSource, mutableTarget);
		mutableSource.addOutEdge(edge);
		mutableTarget.addInEdge(edge);
		edges.add(edge);
		return edge;
	}

	public void removeEdge(final CfaEdge edge) {
		checkNotNull(edge);
		checkArgument(edges.contains(edge));

		final CfaLoc source = edge.getSource();
		final CfaLoc target = edge.getTarget();

		checkNotNull(source);
		checkNotNull(target);

		final CfaLoc mutableSource = source;
		final CfaLoc mutableTarget = target;

		mutableSource.removeOutEdge(edge);
		mutableTarget.removeInEdge(edge);
		edges.remove(edge);
	}

}
