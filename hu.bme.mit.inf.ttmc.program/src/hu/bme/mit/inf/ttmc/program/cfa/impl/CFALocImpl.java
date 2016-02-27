package hu.bme.mit.inf.ttmc.program.cfa.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;
import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;

public class CFALocImpl implements CFALoc {

	private final CFA cfa;
	private final Collection<CFAEdge> inEdges;
	private final Collection<CFAEdge> outEdges;
	
	CFALocImpl(final CFA cfa) {
		this.cfa = checkNotNull(cfa);
		inEdges = new ArrayList<>();
		outEdges = new ArrayList<>();
	}
	
	@Override
	public CFA getCFA() {
		return cfa;
	}
	
	@Override
	public Collection<CFAEdge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	@Override
	public Collection<CFAEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}
	
	////
	
	void addInEdge(final CFAEdge edge) {
		inEdges.add(edge);
	}
	
	void addOutEdge(final CFAEdge edge) {
		outEdges.add(edge);
	}

}
