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
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;
import hu.bme.mit.theta.formalism.common.Automaton;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class CFA implements Automaton<CfaLoc, CfaEdge> {

	private CfaLoc initLoc;
	private CfaLoc finalLoc;
	private CfaLoc errorLoc;

	private final Collection<CfaLoc> locs;
	private final Collection<CfaEdge> edges;

	public CFA() {
		locs = new HashSet<>();
		edges = new LinkedList<>();
	}

	////

	@Override
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

	@Override
	public Collection<CfaLoc> getLocs() {
		return Collections.unmodifiableCollection(locs);
	}

	public CfaLoc createLoc(final String name) {
		final CfaLoc loc = new CfaLoc(name);
		locs.add(loc);
		return loc;
	}

	////

	@Override
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
		return edge;
	}

	/*
	 * Location
	 */

	public static final class CfaLoc implements Loc<CfaLoc, CfaEdge> {
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

		@Override
		public Collection<CfaEdge> getInEdges() {
			return Collections.unmodifiableCollection(inEdges);
		}

		@Override
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

	public static final class CfaEdge implements Edge<CfaLoc, CfaEdge> {
		private final CfaLoc source;
		private final CfaLoc target;
		private final List<Stmt> stmts;

		private CfaEdge(final CfaLoc source, final CfaLoc target, final List<? extends Stmt> stmts) {
			this.source = source;
			this.target = target;
			this.stmts = ImmutableList.copyOf(stmts);
		}

		@Override
		public CfaLoc getSource() {
			return source;
		}

		@Override
		public CfaLoc getTarget() {
			return target;
		}

		public List<Stmt> getStmts() {
			return stmts;
		}
	}

}
