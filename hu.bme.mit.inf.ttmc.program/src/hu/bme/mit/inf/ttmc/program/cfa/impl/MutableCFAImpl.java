package hu.bme.mit.inf.ttmc.program.cfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;

public class MutableCFAImpl implements CFA {

	private MutableCFALocImpl initLoc;
	private MutableCFALocImpl finalLoc;
	private MutableCFALocImpl errorLoc;
	
	private final Collection<MutableCFALocImpl> locs;
	private final Collection<MutableCFAEdgeImpl> edges;
	
	public MutableCFAImpl() {		
		locs = new HashSet<>();
		edges = new HashSet<>();
		
		initLoc = new MutableCFALocImpl(this);
		finalLoc = new MutableCFALocImpl(this);
		errorLoc = new MutableCFALocImpl(this);
		
		locs.add(initLoc);
		locs.add(finalLoc);
		locs.add(errorLoc);
	}
	
	////
	
	@Override
	public MutableCFALocImpl getInitLoc() {
		return initLoc;
	}
	
	public void setInitLoc(final MutableCFALocImpl initLoc) {
		checkNotNull(initLoc);
		checkArgument(initLoc.getCFA() == this);
		this.initLoc = initLoc;
	}
	
	////
	
	@Override
	public MutableCFALocImpl getFinalLoc() {
		return finalLoc;
	}
	
	
	public void setFinalLoc(final MutableCFALocImpl finalLoc) {
		checkNotNull(finalLoc);
		checkArgument(finalLoc.getCFA() == this);
		this.finalLoc = finalLoc;
	}
	
	////
	
	@Override
	public MutableCFALocImpl getErrorLoc() {
		return errorLoc;
	}
	
	public void setErrorLoc(final MutableCFALocImpl errorLoc) {
		checkNotNull(errorLoc);
		checkArgument(errorLoc.getCFA() == this);
		this.errorLoc = errorLoc;
	}
	
	////
	
	@Override
	public Collection<MutableCFALocImpl> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}
	
	public MutableCFALocImpl createLoc() {
		final MutableCFALocImpl loc = new MutableCFALocImpl(this);
		locs.add(loc);
		return loc;
	}
	
	public void deleteLoc(final MutableCFALocImpl loc) {
		checkNotNull(loc);
		checkArgument(loc.getCFA() == this);
		checkArgument(loc != initLoc);
		checkArgument(loc != finalLoc);
		checkArgument(loc != errorLoc);
		checkArgument(loc.getInEdges().isEmpty());
		checkArgument(loc.getOutEdges().isEmpty());
		loc.setCFA(null);
		locs.remove(loc);
	}
	
	////
	
	@Override
	public Collection<MutableCFAEdgeImpl> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}
	
	public MutableCFAEdgeImpl createEdge(final MutableCFALocImpl source, final MutableCFALocImpl target) {
		checkNotNull(source);
		checkNotNull(target);
		checkArgument(source.getCFA() == this);
		checkArgument(target.getCFA() == this);
		
		final MutableCFAEdgeImpl edge = new MutableCFAEdgeImpl(this, source, target);
		source.addOutEdge(edge);
		target.addOutEdge(edge);
		edges.add(edge);
		return edge;
	}
	
	public void deleteEdge(final MutableCFAEdgeImpl edge) {
		checkNotNull(edge);
		checkArgument(edge.getCFA() == this);
		edge.getSource().removeOutEdge(edge);
		edge.getTarget().removeInEdge(edge);
		edge.setCFA(null);
		edges.remove(edge);
	}
	
}
