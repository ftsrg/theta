package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismUtils;

public final class SimpleTCFA implements TCFA {

	private final Collection<TCFALoc> locs;
	private final Collection<TCFAEdge> edges;

	private TCFALoc initLoc;

	private final Collection<VarDecl<?>> dataVars;
	private final Collection<ClockDecl> clockVars;

	public SimpleTCFA() {
		locs = new HashSet<>();
		edges = new HashSet<>();
		dataVars = new HashSet<>();
		clockVars = new HashSet<>();
	}

	////

	@Override
	public Collection<? extends VarDecl<?>> getDataVars() {
		return Collections.unmodifiableCollection(dataVars);
	}

	@Override
	public Collection<? extends ClockDecl> getClockVars() {
		return Collections.unmodifiableCollection(clockVars);
	}

	////

	@Override
	public TCFALoc getInitLoc() {
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
		final SimpleTCFALoc loc = new SimpleTCFALoc(name, urgent, invars);

		invars.forEach(this::addVars);

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

		final SimpleTCFALoc mutableSource = (SimpleTCFALoc) source;
		final SimpleTCFALoc mutableTarget = (SimpleTCFALoc) target;

		final SimpleTCFAEdge edge = new SimpleTCFAEdge(mutableSource, mutableTarget, stmts);
		mutableSource.outEdges.add(edge);
		mutableTarget.inEdges.add(edge);

		stmts.forEach(this::addVars);

		edges.add(edge);
		return edge;
	}

	private void addVars(final Stmt stmt) {
		final Collection<VarDecl<?>> varDecls = FormalismUtils.getVars(stmt);
		varDecls.forEach(this::addVar);
	}

	private void addVars(final Expr<?> expr) {
		final Collection<VarDecl<?>> varDecls = FormalismUtils.getVars(expr);
		varDecls.forEach(this::addVar);
	}

	private void addVar(final VarDecl<?> varDecl) {
		if (varDecl instanceof ClockDecl) {
			final ClockDecl clockDecl = (ClockDecl) varDecl;
			clockVars.add(clockDecl);
		} else {
			dataVars.add(varDecl);
		}
	}

}
