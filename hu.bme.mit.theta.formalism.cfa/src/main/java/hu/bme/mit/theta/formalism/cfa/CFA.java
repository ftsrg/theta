package hu.bme.mit.theta.formalism.cfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.StmtUtils;

public final class CFA {

	private CfaLoc initLoc;
	private CfaLoc finalLoc;
	private CfaLoc errorLoc;

	private final Collection<VarDecl<?>> vars;
	private final Collection<CfaLoc> locs;
	private final Collection<CfaEdge> edges;

	public CFA() {
		vars = new HashSet<>();
		locs = new HashSet<>();
		edges = new LinkedList<>();
	}

	////

	public CfaLoc getInitLoc() {
		return initLoc;
	}

	public void setInitLoc(final CfaLoc initLoc) {
		checkNotNull(initLoc);
		checkArgument(locs.contains(initLoc));
		this.initLoc = initLoc;
	}

	////

	public CfaLoc getFinalLoc() {
		return finalLoc;
	}

	public void setFinalLoc(final CfaLoc finalLoc) {
		checkNotNull(finalLoc);
		checkArgument(locs.contains(finalLoc));
		this.finalLoc = finalLoc;
	}

	////

	public CfaLoc getErrorLoc() {
		return errorLoc;
	}

	public void setErrorLoc(final CfaLoc errorLoc) {
		checkNotNull(errorLoc);
		checkArgument(locs.contains(errorLoc));
		this.errorLoc = errorLoc;
	}

	////

	public Collection<VarDecl<?>> getVars() {
		return Collections.unmodifiableCollection(vars);
	}

	////

	public Collection<CfaLoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	public CfaLoc createLoc(final String name) {
		final CfaLoc loc = new CfaLoc(name);
		locs.add(loc);
		return loc;
	}

	////

	public Collection<CfaEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public CfaEdge createEdge(final CfaLoc source, final CfaLoc target, final List<? extends Stmt> stmts) {
		checkNotNull(source);
		checkNotNull(target);
		checkNotNull(stmts);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));

		final CfaEdge edge = new CfaEdge(source, target, stmts);
		source.outEdges.add(edge);
		target.inEdges.add(edge);
		edges.add(edge);
		vars.addAll(StmtUtils.getVars(stmts));
		return edge;
	}

	/*
	 * Location
	 */

	public static final class CfaLoc {
		private final String name;
		private final Collection<CfaEdge> inEdges;
		private final Collection<CfaEdge> outEdges;

		private CfaLoc(final String name) {
			this.name = name;
			inEdges = new LinkedList<>();
			outEdges = new LinkedList<>();
		}

		////

		public String getName() {
			return name;
		}

		public Collection<CfaEdge> getInEdges() {
			return Collections.unmodifiableCollection(inEdges);
		}

		public Collection<CfaEdge> getOutEdges() {
			return Collections.unmodifiableCollection(outEdges);
		}

		////

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(name).toString();
		}
	}

	/*
	 * Edge
	 */

	public static final class CfaEdge {
		private final CfaLoc source;
		private final CfaLoc target;
		private final List<Stmt> stmts;

		private CfaEdge(final CfaLoc source, final CfaLoc target, final List<? extends Stmt> stmts) {
			this.source = source;
			this.target = target;
			this.stmts = ImmutableList.copyOf(stmts);
		}

		public CfaLoc getSource() {
			return source;
		}

		public CfaLoc getTarget() {
			return target;
		}

		public List<Stmt> getStmts() {
			return stmts;
		}
	}

}
