package hu.bme.mit.inf.ttmc.program.cfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;

public class MutableCFALoc implements CFALoc {

	private final Collection<MutableCFAEdge> inEdges;
	private final Collection<MutableCFAEdge> outEdges;
	
	
	MutableCFALoc() {
		inEdges = new HashSet<>();
		outEdges = new HashSet<>();
	}

	////
	
	@Override
	public Collection<MutableCFAEdge> getInEdges() {	
		return Collections.unmodifiableCollection(inEdges);
	}
	
	void addInEdge(final MutableCFAEdge edge) {
		inEdges.add(edge);
	}
	
	void removeInEdge(final MutableCFAEdge edge) {
		inEdges.remove(edge);
	}
	
	////

	@Override
	public Collection<MutableCFAEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}
	
	void addOutEdge(final MutableCFAEdge edge) {
		outEdges.add(edge);
	}
	
	void removeOutEdge(final MutableCFAEdge edge) {
		outEdges.remove(edge);
	}
	
}
