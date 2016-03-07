package hu.bme.mit.inf.ttmc.program.cfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;

public class MutableCFA implements CFA {

	private MutableCFALoc initLoc;
	private MutableCFALoc finalLoc;
	private MutableCFALoc errorLoc;
	
	private final Collection<MutableCFALoc> locs;
	private final Collection<MutableCFAEdge> edges;
	
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
	public MutableCFALoc getInitLoc() {
		return initLoc;
	}
	
	public void setInitLoc(final MutableCFALoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}
	
	////
	
	@Override
	public MutableCFALoc getFinalLoc() {
		return finalLoc;
	}
	
	
	public void setFinalLoc(final MutableCFALoc finalLoc) {
		checkNotNull(finalLoc);
		checkArgument(locs.contains(finalLoc));
		this.finalLoc = finalLoc;
	}
	
	////
	
	@Override
	public MutableCFALoc getErrorLoc() {
		return errorLoc;
	}
	
	public void setErrorLoc(final MutableCFALoc errorLoc) {
		checkNotNull(errorLoc);
		checkArgument(locs.contains(errorLoc));
		this.errorLoc = errorLoc;
	}
	
	////
	
	@Override
	public Collection<MutableCFALoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}
	
	public MutableCFALoc createLoc() {
		final MutableCFALoc loc = new MutableCFALoc();
		locs.add(loc);
		return loc;
	}
	
	public void deleteLoc(final MutableCFALoc loc) {
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
	public Collection<MutableCFAEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}
	
	public MutableCFAEdge createEdge(final MutableCFALoc source, final MutableCFALoc target) {
		checkNotNull(source);
		checkNotNull(target);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));
		
		final MutableCFAEdge edge = new MutableCFAEdge(source, target);
		source.addOutEdge(edge);
		target.addOutEdge(edge);
		edges.add(edge);
		return edge;
	}
	
	public void deleteEdge(final MutableCFAEdge edge) {
		checkNotNull(edge);
		checkArgument(edges.contains(edge));
		edge.getSource().removeOutEdge(edge);
		edge.getTarget().removeInEdge(edge);
		edges.remove(edge);
	}
	
}
