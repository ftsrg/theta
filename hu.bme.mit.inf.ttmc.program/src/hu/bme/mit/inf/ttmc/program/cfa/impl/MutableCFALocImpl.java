package hu.bme.mit.inf.ttmc.program.cfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;

public class MutableCFALocImpl implements CFALoc {

	private final Collection<MutableCFAEdgeImpl> inEdges;
	private final Collection<MutableCFAEdgeImpl> outEdges;
	
	
	MutableCFALocImpl() {
		inEdges = new HashSet<>();
		outEdges = new HashSet<>();
	}

	////
	
	@Override
	public Collection<MutableCFAEdgeImpl> getInEdges() {	
		return Collections.unmodifiableCollection(inEdges);
	}
	
	void addInEdge(final MutableCFAEdgeImpl edge) {
		inEdges.add(edge);
	}
	
	void removeInEdge(final MutableCFAEdgeImpl edge) {
		inEdges.remove(edge);
	}
	
	////

	@Override
	public Collection<MutableCFAEdgeImpl> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}
	
	void addOutEdge(final MutableCFAEdgeImpl edge) {
		outEdges.add(edge);
	}
	
	void removeOutEdge(final MutableCFAEdgeImpl edge) {
		outEdges.remove(edge);
	}
	
}
