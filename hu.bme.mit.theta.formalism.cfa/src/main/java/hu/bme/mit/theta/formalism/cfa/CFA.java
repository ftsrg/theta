package hu.bme.mit.theta.formalism.cfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.StmtUtils;

/**
 * Represents a mutable Control Flow Automata (CFA).
 */
public final class CFA {

	private Loc initLoc;
	private Loc finalLoc;
	private Loc errorLoc;

	private final Collection<VarDecl<?>> vars;
	private final Collection<Loc> locs;
	private final Collection<Edge> edges;

	public CFA() {
		vars = new HashSet<>();
		locs = new HashSet<>();
		edges = new LinkedList<>();
	}

	////

	public Loc getInitLoc() {
		return initLoc;
	}

	public void setInitLoc(final Loc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////

	public Loc getFinalLoc() {
		return finalLoc;
	}

	public void setFinalLoc(final Loc finalLoc) {
		checkNotNull(finalLoc);
		checkArgument(locs.contains(finalLoc));
		this.finalLoc = finalLoc;
	}

	////

	public Loc getErrorLoc() {
		return errorLoc;
	}

	public void setErrorLoc(final Loc errorLoc) {
		checkNotNull(errorLoc);
		checkArgument(locs.contains(errorLoc));
		this.errorLoc = errorLoc;
	}

	////

	public Collection<VarDecl<?>> getVars() {
		return Collections.unmodifiableCollection(vars);
	}

	////

	public Collection<Loc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	public Loc createLoc(final String name) {
		final Loc loc = new Loc(name);
		locs.add(loc);
		return loc;
	}

	////

	public Collection<Edge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public Edge createEdge(final Loc source, final Loc target, final List<? extends Stmt> stmts) {
		checkNotNull(source);
		checkNotNull(target);
		checkNotNull(stmts);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));

		final Edge edge = new Edge(source, target, stmts);
		source.outEdges.add(edge);
		target.inEdges.add(edge);
		edges.add(edge);
		vars.addAll(StmtUtils.getVars(stmts));
		return edge;
	}

	/*
	 * Location
	 */

	public static final class Loc {
		private final String name;
		private final Collection<Edge> inEdges;
		private final Collection<Edge> outEdges;

		private Loc(final String name) {
			this.name = name;
			inEdges = new LinkedList<>();
			outEdges = new LinkedList<>();
		}

		////

		public String getName() {
			return name;
		}

		public Collection<Edge> getInEdges() {
			return Collections.unmodifiableCollection(inEdges);
		}

		public Collection<Edge> getOutEdges() {
			return Collections.unmodifiableCollection(outEdges);
		}

		////

		@Override
		public String toString() {
			return Utils.toStringBuilder(getClass().getSimpleName()).add(name).toString();
		}
	}

	/*
	 * Edge
	 */

	public static final class Edge {
		private final Loc source;
		private final Loc target;
		private final List<Stmt> stmts;

		private Edge(final Loc source, final Loc target, final List<? extends Stmt> stmts) {
			this.source = source;
			this.target = target;
			this.stmts = ImmutableList.copyOf(stmts);
		}

		public Loc getSource() {
			return source;
		}

		public Loc getTarget() {
			return target;
		}

		public List<Stmt> getStmts() {
			return stmts;
		}
	}

}
