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
package hu.bme.mit.theta.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;

public final class XtaProcess {
	private final String name;
	private final Collection<VarDecl<?>> dataVars;
	private final Collection<VarDecl<RatType>> clockVars;
	private final Collection<Loc> locs;
	private final Collection<Edge> edges;
	private Loc initLoc;

	private final Collection<VarDecl<?>> unmodDataVars;
	private final Collection<VarDecl<RatType>> unmodClockVars;
	private final Collection<Loc> unmodLocs;
	private final Collection<Edge> unmodEdges;

	////

	private XtaProcess(final String name) {
		this.name = checkNotNull(name);
		dataVars = new HashSet<>();
		clockVars = new HashSet<>();
		locs = new HashSet<>();
		edges = new ArrayList<>();

		unmodDataVars = Collections.unmodifiableCollection(dataVars);
		unmodClockVars = Collections.unmodifiableCollection(clockVars);
		unmodLocs = Collections.unmodifiableCollection(locs);
		unmodEdges = Collections.unmodifiableCollection(edges);
	}

	public static XtaProcess create(final String name) {
		return new XtaProcess(name);
	}

	////

	public String getName() {
		return name;
	}

	public Collection<VarDecl<?>> getDataVars() {
		return unmodDataVars;
	}

	public Collection<VarDecl<RatType>> getClockVars() {
		return unmodClockVars;
	}

	public Collection<Loc> getLocs() {
		return unmodLocs;
	}

	public Collection<Edge> getEdges() {
		return unmodEdges;
	}

	public Loc getInitLoc() {
		checkNotNull(initLoc);
		return initLoc;
	}

	////

	public void addDataVar(final VarDecl<?> varDecl) {
		checkNotNull(varDecl);
		checkArgument(!clockVars.contains(varDecl));
		dataVars.add(varDecl);
	}

	public void addClockVar(final VarDecl<RatType> varDecl) {
		checkNotNull(varDecl);
		checkArgument(!dataVars.contains(varDecl));
		clockVars.add(varDecl);
	}

	public void setInitLoc(final Loc loc) {
		checkNotNull(loc);
		checkArgument(locs.contains(loc));
		this.initLoc = loc;
	}

	public Loc createLoc(final String name, final LocKind kind, final Collection<Expr<BoolType>> invars) {
		final Loc loc = new Loc(name, kind, invars);
		locs.add(loc);
		return loc;
	}

	public Edge createEdge(final Loc source, final Loc target, final Collection<Expr<BoolType>> guards,
						   final Optional<Sync> sync, final List<Stmt> updates) {
		checkArgument(locs.contains(source));
		checkArgument(locs.contains(target));
		final Edge edge = new Edge(source, target, guards, sync, updates);
		source.outEdges.add(edge);
		target.inEdges.add(edge);
		return edge;
	}

	////

	private Collection<Guard> createGuards(final Collection<Expr<BoolType>> exprs) {
		checkNotNull(exprs);

		final ImmutableList.Builder<Guard> builder = ImmutableList.builder();
		for (final Expr<BoolType> expr : exprs) {
			final Collection<VarDecl<?>> vars = ExprUtils.getVars(expr);

			boolean dataExpr = false;
			boolean clockExpr = false;
			for (final VarDecl<?> varDecl : vars) {
				if (dataVars.contains(varDecl)) {
					dataExpr = true;
				} else if (clockVars.contains(varDecl)) {
					clockExpr = true;
				} else {
					throw new IllegalArgumentException("Undeclared variable: " + varDecl.getName());
				}
			}

			final Guard guard;
			if (dataExpr && !clockExpr) {
				guard = Guard.dataGuard(expr);
			} else if (!dataExpr && clockExpr) {
				guard = Guard.clockGuard(expr);
			} else {
				throw new UnsupportedOperationException();
			}
			builder.add(guard);
		}
		return builder.build();
	}

	private List<Update> createUpdates(final List<Stmt> stmts) {
		checkNotNull(stmts);

		final ImmutableList.Builder<Update> builder = ImmutableList.builder();
		for (final Stmt stmt : stmts) {
			final Collection<VarDecl<?>> varsDecls = StmtUtils.getVars(stmt);
			boolean dataStmt = false;
			boolean clockStmt = false;
			for (final VarDecl<?> varDecl : varsDecls) {
				if (dataVars.contains(varDecl)) {
					dataStmt = true;
				} else if (clockVars.contains(varDecl)) {
					clockStmt = true;
				} else {
					throw new IllegalArgumentException("Undeclared variable: " + varDecl.getName());
				}
			}

			final Update update;
			if (dataStmt && !clockStmt) {
				update = Update.dataUpdate(stmt);
			} else if (!dataStmt && clockStmt) {
				update = Update.clockUpdate(stmt);
			} else {
				throw new UnsupportedOperationException();
			}
			builder.add(update);
		}
		return builder.build();
	}

	////

	public enum LocKind {
		NORMAL, URGENT, COMMITTED;
	}

	public final class Loc {
		private final Collection<Edge> inEdges;
		private final Collection<Edge> outEdges;
		private final String name;
		private final LocKind kind;
		private final Collection<Guard> invars;

		private final Collection<Edge> unmodInEdges;
		private final Collection<Edge> unmodOutEdges;

		private Loc(final String name, final LocKind kind, final Collection<Expr<BoolType>> invars) {
			inEdges = new ArrayList<>();
			outEdges = new ArrayList<>();
			this.name = checkNotNull(name);
			this.kind = checkNotNull(kind);
			this.invars = createGuards(invars);

			unmodInEdges = Collections.unmodifiableCollection(inEdges);
			unmodOutEdges = Collections.unmodifiableCollection(outEdges);
		}

		public Collection<Edge> getInEdges() {
			return unmodInEdges;
		}

		public Collection<Edge> getOutEdges() {
			return unmodOutEdges;
		}

		public String getName() {
			return name;
		}

		public LocKind getKind() {
			return kind;
		}

		public Collection<Guard> getInvars() {
			return invars;
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder("loc").add(name).toString();
		}
	}

	////

	public final class Edge {
		private final Loc source;
		private final Loc target;
		private final Collection<Guard> guards;
		private final Optional<Sync> sync;
		private final List<Update> updates;

		private Edge(final Loc source, final Loc target, final Collection<Expr<BoolType>> guards,
					 final Optional<Sync> sync, final List<Stmt> updates) {
			this.source = checkNotNull(source);
			this.target = checkNotNull(target);
			this.guards = createGuards(guards);
			this.sync = checkNotNull(sync);
			this.updates = createUpdates(updates);
		}

		public Loc getSource() {
			return source;
		}

		public Loc getTarget() {
			return target;
		}

		public Collection<Guard> getGuards() {
			return guards;
		}

		public Optional<Sync> getSync() {
			return sync;
		}

		public List<Update> getUpdates() {
			return updates;
		}
	}

}
