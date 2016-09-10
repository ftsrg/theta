package hu.bme.mit.theta.formalism.tcfa.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.utils.FormalismUtils;

public final class SimpleTcfa implements TCFA {

	private final Collection<TcfaLoc> locs;
	private final Collection<TcfaEdge> edges;

	private TcfaLoc initLoc;

	private final Collection<VarDecl<?>> dataVars;
	private final Collection<ClockDecl> clockVars;

	public SimpleTcfa() {
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
	public TcfaLoc getInitLoc() {
		return initLoc;
	}

	public void setInitLoc(final TcfaLoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////

	@Override
	public Collection<? extends TcfaLoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	public TcfaLoc createLoc(final String name, final boolean urgent,
			final Collection<? extends Expr<? extends BoolType>> invars) {
		checkNotNull(name);
		checkNotNull(invars);
		final SimpleTcfaLoc loc = new SimpleTcfaLoc(name, urgent, invars);

		invars.forEach(this::addVars);

		locs.add(loc);
		return loc;
	}

	////

	@Override
	public Collection<? extends TcfaEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public TcfaEdge createEdge(final TcfaLoc source, final TcfaLoc target, final List<? extends Stmt> stmts) {
		checkNotNull(source);
		checkNotNull(target);
		checkNotNull(stmts);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));

		final SimpleTcfaLoc mutableSource = (SimpleTcfaLoc) source;
		final SimpleTcfaLoc mutableTarget = (SimpleTcfaLoc) target;

		final SimpleTcfaEdge edge = new SimpleTcfaEdge(mutableSource, mutableTarget, stmts);
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
