package hu.bme.mit.theta.formalism.cfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;
import hu.bme.mit.theta.formalism.common.Automaton;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class CFA implements Automaton<CfaLoc, CfaEdge> {
	private int nextId;

	private CfaLoc initLoc;
	private CfaLoc finalLoc;
	private CfaLoc errorLoc;

	private final Collection<CfaLoc> locs;
	private final Collection<CfaEdge> edges;

	public CFA() {
		locs = new HashSet<>();
		edges = new HashSet<>();
		nextId = 0;
		initLoc = createLoc();
		finalLoc = createLoc();
		errorLoc = createLoc();
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

	public CfaLoc createLoc() {
		final CfaLoc loc = new CfaLoc(nextId + "");
		++nextId;
		locs.add(loc);
		return loc;
	}

	public void removeLoc(final CfaLoc loc) {
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
	public Collection<CfaEdge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}

	public CfaEdge createEdge(final CfaLoc source, final CfaLoc target) {
		checkNotNull(source);
		checkNotNull(target);
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));

		final CfaLoc mutableSource = source;
		final CfaLoc mutableTarget = target;

		final CfaEdge edge = new CfaEdge(mutableSource, mutableTarget);
		mutableSource.addOutEdge(edge);
		mutableTarget.addInEdge(edge);
		edges.add(edge);
		return edge;
	}

	public void removeEdge(final CfaEdge edge) {
		checkNotNull(edge);
		checkArgument(edges.contains(edge));

		final CfaLoc source = edge.getSource();
		final CfaLoc target = edge.getTarget();

		checkNotNull(source);
		checkNotNull(target);

		final CfaLoc mutableSource = source;
		final CfaLoc mutableTarget = target;

		mutableSource.removeOutEdge(edge);
		mutableTarget.removeInEdge(edge);
		edges.remove(edge);
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
			inEdges = new HashSet<>();
			outEdges = new HashSet<>();
		}

		////

		@Override
		public Collection<CfaEdge> getInEdges() {
			return Collections.unmodifiableCollection(inEdges);
		}

		void addInEdge(final CfaEdge edge) {
			inEdges.add(edge);
		}

		void removeInEdge(final CfaEdge edge) {
			inEdges.remove(edge);
		}

		////

		@Override
		public Collection<CfaEdge> getOutEdges() {
			return Collections.unmodifiableCollection(outEdges);
		}

		void addOutEdge(final CfaEdge edge) {
			outEdges.add(edge);
		}

		void removeOutEdge(final CfaEdge edge) {
			outEdges.remove(edge);
		}

		public String getName() {
			return name;
		}

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

		private CfaEdge(final CfaLoc source, final CfaLoc target) {
			this.source = source;
			this.target = target;
			stmts = new ArrayList<>();
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
