package hu.bme.mit.inf.ttmc.formalism.cfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;

class MutableCFALoc implements CFALoc {

	private final Collection<CFAEdge> inEdges;
	private final Collection<CFAEdge> outEdges;
	
	
	MutableCFALoc() {
		inEdges = new HashSet<>();
		outEdges = new HashSet<>();
	}

	////
	
	@Override
	public Collection<CFAEdge> getInEdges() {	
		return Collections.unmodifiableCollection(inEdges);
	}
	
	void addInEdge(final CFAEdge edge) {
		inEdges.add(edge);
	}
	
	void removeInEdge(final CFAEdge edge) {
		inEdges.remove(edge);
	}
	
	////

	@Override
	public Collection<CFAEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}
	
	void addOutEdge(final CFAEdge edge) {
		outEdges.add(edge);
	}
	
	void removeOutEdge(final CFAEdge edge) {
		outEdges.remove(edge);
	}
	
}
