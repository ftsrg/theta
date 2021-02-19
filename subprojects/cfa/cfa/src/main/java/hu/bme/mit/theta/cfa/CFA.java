/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.cfa;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static com.google.common.collect.ImmutableSet.toImmutableSet;
import static java.lang.String.format;

import java.util.*;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.StmtUtils;

/**
 * Represents an immutable Control Flow Automata (CFA). Use the builder class to
 * create a new instance.
 */
public final class CFA {

	private final Loc initLoc;
	private final Optional<Loc> finalLoc;
	private final Optional<Loc> errorLoc;

	private final Collection<VarDecl<?>> vars;
	private final Collection<Loc> locs;
	private final Collection<Edge> edges;

	private CFA(final Builder builder) {
		initLoc = builder.initLoc;
		finalLoc = Optional.ofNullable(builder.finalLoc);
		errorLoc = Optional.ofNullable(builder.errorLoc);
		locs = ImmutableSet.copyOf(builder.locs);
		edges = ImmutableList.copyOf(builder.edges);
		vars = edges.stream().flatMap(e -> StmtUtils.getVars(e.getStmt()).stream()).collect(toImmutableSet());
	}

	public Loc getInitLoc() {
		return initLoc;
	}

	public Optional<Loc> getFinalLoc() {
		return finalLoc;
	}

	public Optional<Loc> getErrorLoc() {
		return errorLoc;
	}

	/**
	 * Get the variables appearing on the edges of the CFA.
	 */
	public Collection<VarDecl<?>> getVars() {
		return vars;
	}

	public Collection<Loc> getLocs() {
		return locs;
	}

	public Collection<Edge> getEdges() {
		return edges;
	}

	public static Builder builder() {
		return new Builder();
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder("process").aligned().addAll(vars).body()
				.addAll(locs.stream().map(this::locToString)).addAll(edges.stream().map(this::edgeToString)).toString();
	}

	private String locToString(final Loc loc) {
		if (initLoc.equals(loc)) {
			return format("(init %s)", loc.getName());
		} else if (finalLoc.isPresent() && finalLoc.get().equals(loc)) {
			return format("(final %s)", loc.getName());
		} else if (errorLoc.isPresent() && errorLoc.get().equals(loc)) {
			return format("(error %s)", loc.getName());
		} else {
			return format("(loc %s)", loc.getName());
		}
	}

	private String edgeToString(final Edge edge) {
		return Utils.lispStringBuilder("edge").add(edge.getSource().getName()).add(edge.getTarget().getName())
				.add(edge.getStmt()).toString();
	}

	public static final class Loc {
		private final String name;
		private final Collection<Edge> inEdges;
		private final Collection<Edge> outEdges;

		private Loc(final String name) {
			this.name = checkNotNull(name);
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
			return name;
		}
	}

	public static final class Edge {
		private final Loc source;
		private final Loc target;
		private final Stmt stmt;

		private Edge(final Loc source, final Loc target, final Stmt stmt) {
			this.source = checkNotNull(source);
			this.target = checkNotNull(target);
			this.stmt = checkNotNull(stmt);
		}

		public Loc getSource() {
			return source;
		}

		public Loc getTarget() {
			return target;
		}

		public Stmt getStmt() {
			return stmt;
		}
	}

	public static final class Builder {
		private Loc initLoc;
		private Loc finalLoc;
		private Loc errorLoc;

		private final Collection<Loc> locs;
		private final Collection<Edge> edges;

		private boolean built;

		private Builder() {
			locs = new HashSet<>();
			edges = new LinkedList<>();
			built = false;
		}

		public Loc getInitLoc() {
			return initLoc;
		}

		public Loc getFinalLoc() {
			return finalLoc;
		}

		public Loc getErrorLoc() {
			return errorLoc;
		}

		public void setInitLoc(final Loc initLoc) {
			checkNotBuilt();
			checkNotNull(initLoc);
			checkArgument(locs.contains(initLoc), "Initial location not present in CFA.");
			checkArgument(!initLoc.equals(finalLoc), "Initial location cannot be same as final.");
			checkArgument(!initLoc.equals(errorLoc), "Initial location cannot be same as error.");
			this.initLoc = initLoc;
		}

		public void setFinalLoc(final Loc finalLoc) {
			checkNotBuilt();
			checkNotNull(finalLoc);
			checkArgument(locs.contains(finalLoc), "Final location not present in CFA.");
			checkArgument(!finalLoc.equals(initLoc), "Final location cannot be same as init.");
			checkArgument(!finalLoc.equals(errorLoc), "Final location cannot be same as error.");
			this.finalLoc = finalLoc;
		}

		public void setErrorLoc(final Loc errorLoc) {
			checkNotBuilt();
			checkNotNull(errorLoc);
			checkArgument(locs.contains(errorLoc), "Error location not present in CFA.");
			checkArgument(!errorLoc.equals(initLoc), "Error location cannot be same as init.");
			checkArgument(!errorLoc.equals(finalLoc), "Error location cannot be same as final.");
			this.errorLoc = errorLoc;
		}

		public Loc createLoc(final String name) {
			checkNotBuilt();
			final Loc loc = new Loc(name);
			locs.add(loc);
			return loc;
		}

		public Edge createEdge(final Loc source, final Loc target, final Stmt stmt) {
			checkNotBuilt();
			checkArgument(locs.contains(source), "Invalid source.");
			checkArgument(locs.contains(target), "Invalid target.");

			final Edge edge = new Edge(source, target, stmt);
			source.outEdges.add(edge);
			target.inEdges.add(edge);
			edges.add(edge);
			return edge;
		}

		public CFA build() {
			checkState(initLoc != null, "Initial location must be set.");
			if (finalLoc != null)
				checkState(finalLoc.getOutEdges().isEmpty(), "Final location cannot have outgoing edges.");
			if (errorLoc != null)
				checkState(errorLoc.getOutEdges().isEmpty(), "Error location cannot have outgoing edges.");
			built = true;
			return new CFA(this);
		}

		private void checkNotBuilt() {
			checkState(!built, "A CFA was already built.");
		}
	}

}
