package hu.bme.mit.theta.formalism.cfa;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.common.Loc;

public final class CfaLoc implements Loc<CfaLoc, CfaEdge> {

	private final String name;

	private final Collection<CfaEdge> inEdges;
	private final Collection<CfaEdge> outEdges;

	CfaLoc(final String name) {
		this.name = name;
		inEdges = new HashSet<>();
		outEdges = new HashSet<>();
	}

	////

	@Override
	public Collection<CfaEdge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	void addInEdge(final CfaEdge edge) {
		inEdges.add(edge);
	}

	void removeInEdge(final CfaEdge edge) {
		inEdges.remove(edge);
	}

	////

	@Override
	public Collection<CfaEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

	void addOutEdge(final CfaEdge edge) {
		outEdges.add(edge);
	}

	void removeOutEdge(final CfaEdge edge) {
		outEdges.remove(edge);
	}

	public String getName() {
		return name;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(name).toString();
	}

}
