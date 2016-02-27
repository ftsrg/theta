package hu.bme.mit.inf.ttmc.program.cfa.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;
import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.program.stmt.Stmt;

public class CFAImpl implements CFA {

	private final CFALoc initLoc;
	private final CFALoc finalLoc;
	private final CFALoc errorLoc;
	
	private final Collection<CFALoc> locs;
	private final Collection<CFAEdge> edges;

	public CFAImpl() {
		locs = new ArrayList<>();
		edges = new ArrayList<>();
		
		this.initLoc = createLoc();
		this.finalLoc = createLoc();
		this.errorLoc = createLoc();
	}

	@Override
	public CFALoc getInitLoc() {
		return initLoc;
	}
	
	@Override
	public CFALoc getFinalLoc() {
		return finalLoc;
	}

	public CFALoc getErrorLoc() {
		return errorLoc;
	}

	@Override
	public Collection<CFALoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	@Override
	public Collection<CFAEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}
	
	////
	
	public CFALoc createLoc() {
		final CFALoc loc = new CFALocImpl(this);
		locs.add(loc);
		return loc;
	}
	
	public CFAEdge createEdge(final CFALoc source, final CFALoc target, final List<Stmt> stmts) {
		final CFAEdge edge = new CFAEdgeImpl(this, source, target, stmts);
		edges.add(edge);
		((CFALocImpl) source).addOutEdge(edge);
		((CFALocImpl) target).addInEdge(edge);
		return edge;
	}

}
