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
		
		initLoc = new MutableCFALocImpl();
		finalLoc = new MutableCFALocImpl();
		errorLoc = new MutableCFALocImpl();
		
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
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}
	
	////
	
	@Override
	public MutableCFALocImpl getFinalLoc() {
		return finalLoc;
	}
	
	
	public void setFinalLoc(final MutableCFALocImpl finalLoc) {
		checkNotNull(finalLoc);
		checkArgument(locs.contains(finalLoc));
		this.finalLoc = finalLoc;
	}
	
	////
	
	@Override
	public MutableCFALocImpl getErrorLoc() {
		return errorLoc;
	}
	
	public void setErrorLoc(final MutableCFALocImpl errorLoc) {
		checkNotNull(errorLoc);
		checkArgument(locs.contains(errorLoc));
		this.errorLoc = errorLoc;
	}
	
	////
	
	@Override
	public Collection<MutableCFALocImpl> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}
	
	public MutableCFALocImpl createLoc() {
		final MutableCFALocImpl loc = new MutableCFALocImpl();
		locs.add(loc);
		return loc;
	}
	
	public void deleteLoc(final MutableCFALocImpl loc) {
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
	public Collection<MutableCFAEdgeImpl> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}
	
	public MutableCFAEdgeImpl createEdge(final MutableCFALocImpl source, final MutableCFALocImpl target) {
		checkNotNull(source);
		checkNotNull(target);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));
		
		final MutableCFAEdgeImpl edge = new MutableCFAEdgeImpl(source, target);
		source.addOutEdge(edge);
		target.addOutEdge(edge);
		edges.add(edge);
		return edge;
	}
	
	public void deleteEdge(final MutableCFAEdgeImpl edge) {
		checkNotNull(edge);
		checkArgument(edges.contains(edge));
		edge.getSource().removeOutEdge(edge);
		edge.getTarget().removeInEdge(edge);
		edges.remove(edge);
	}
	
}
