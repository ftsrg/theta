package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public final class MutableTCFA implements TCFA {

	private final Collection<TCFALoc> locs;
	private final Collection<TCFAEdge> edges;

	private TCFALoc initLoc;

	public MutableTCFA() {
		locs = new LinkedList<>();
		edges = new LinkedList<>();
	}

	////

	@Override
	public Collection<? extends VarDecl<?>> getVars() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	@Override
	public TCFALoc getInitLoc() {
		checkNotNull(initLoc);
		return initLoc;
	}

	public void setInitLoc(final TCFALoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////

	@Override
	public Collection<? extends TCFALoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	public TCFALoc createLoc(final String name, final boolean urgent,
			final Collection<? extends Expr<? extends BoolType>> invars) {
		checkNotNull(name);
		checkNotNull(invars);
		final MutableTCFALoc loc = new MutableTCFALoc(name, urgent, invars);
		locs.add(loc);
		return loc;
	}

	////

	@Override
	public Collection<? extends TCFAEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public TCFAEdge createEdge(final TCFALoc source, final TCFALoc target, final List<? extends Stmt> stmts) {
		checkNotNull(source);
		checkNotNull(target);
		checkNotNull(stmts);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));

		final MutableTCFALoc mutableSource = (MutableTCFALoc) source;
		final MutableTCFALoc mutableTarget = (MutableTCFALoc) target;

		final MutableTCFAEdge edge = new MutableTCFAEdge(mutableSource, mutableTarget, stmts);
		mutableSource.outEdges.add(edge);
		mutableTarget.inEdges.add(edge);
		edges.add(edge);
		return edge;
	}

}
