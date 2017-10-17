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
package hu.bme.mit.theta.formalism.xta.analysis;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.Streams.zip;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Add;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Geq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;
import java.util.stream.Stream;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.Label;
import hu.bme.mit.theta.formalism.xta.Update;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaProcess.LocKind;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public abstract class XtaAction extends StmtAction {

	private static final VarDecl<RatType> DELAY = Var("_delay", Rat());

	private final Collection<VarDecl<RatType>> clockVars;
	private final List<Loc> sourceLocs;

	private XtaAction(final XtaSystem system, final List<Loc> source) {
		checkNotNull(system);
		this.clockVars = system.getClockVars();
		this.sourceLocs = ImmutableList.copyOf(checkNotNull(source));
	}

	public static SimpleXtaAction simple(final XtaSystem system, final List<Loc> sourceLocs, final Edge edge) {
		return new SimpleXtaAction(system, sourceLocs, edge);
	}

	public static SyncedXtaAction synced(final XtaSystem system, final List<Loc> sourceLocs, final Edge emitEdge,
			final Edge recvEdge) {
		return new SyncedXtaAction(system, sourceLocs, emitEdge, recvEdge);
	}

	public Collection<VarDecl<RatType>> getClockVars() {
		return clockVars;
	}

	public List<Loc> getSourceLocs() {
		return sourceLocs;
	}

	public abstract List<Loc> getTargetLocs();

	public boolean isSimple() {
		return false;
	}

	public boolean isSynced() {
		return false;
	}

	public SimpleXtaAction asSimple() {
		throw new ClassCastException();
	}

	public SyncedXtaAction asSynced() {
		throw new ClassCastException();
	}

	public static final class SimpleXtaAction extends XtaAction {
		private final Edge edge;
		private final List<Loc> targetLocs;

		private volatile List<Stmt> stmts = null;

		private SimpleXtaAction(final XtaSystem system, final List<Loc> sourceLocs, final Edge edge) {
			super(system, sourceLocs);
			this.edge = checkNotNull(edge);

			final ImmutableList.Builder<Loc> builder = ImmutableList.builder();
			final Loc source = edge.getSource();
			final Loc target = edge.getTarget();
			boolean matched = false;
			for (final Loc loc : sourceLocs) {
				if (loc.equals(source)) {
					checkArgument(!matched);
					builder.add(target);
					matched = true;
				} else {
					builder.add(loc);
				}
			}
			checkArgument(matched);
			targetLocs = builder.build();
		}

		public Edge getEdge() {
			return edge;
		}

		@Override
		public List<Loc> getTargetLocs() {
			return targetLocs;
		}

		@Override
		public boolean isSimple() {
			return true;
		}

		@Override
		public SimpleXtaAction asSimple() {
			return this;
		}

		@Override
		public List<Stmt> getStmts() {
			List<Stmt> result = stmts;
			if (stmts == null) {
				final ImmutableList.Builder<Stmt> builder = ImmutableList.builder();
				addInvariants(builder, getSourceLocs());
				addGuards(builder, edge);
				addUpdates(builder, edge);
				addInvariants(builder, targetLocs);
				if (shouldApplyDelay(getTargetLocs())) {
					addDelay(builder, getClockVars());
				}
				result = builder.build();
				stmts = result;
			}
			return result;
		}

		@Override
		public String toString() {
			final StringJoiner sj = new StringJoiner("\n");
			edge.getGuards().forEach(g -> sj.add("[" + g + "]"));
			edge.getUpdates().forEach(Update::toString);
			return sj.toString();
		}

	}

	public static final class SyncedXtaAction extends XtaAction {
		private final Edge emitEdge;
		private final Edge recvEdge;
		private final List<Loc> targetLocs;

		private volatile List<Stmt> stmts = null;

		private SyncedXtaAction(final XtaSystem system, final List<Loc> sourceLocs, final Edge emitEdge,
				final Edge recvEdge) {
			super(system, sourceLocs);
			this.emitEdge = checkNotNull(emitEdge);
			this.recvEdge = checkNotNull(recvEdge);

			checkArgument(emitEdge.getSync().isPresent());
			checkArgument(recvEdge.getSync().isPresent());
			final Label emitLabel = emitEdge.getSync().get().getLabel();
			final Label recvLabel = recvEdge.getSync().get().getLabel();
			checkArgument(emitLabel.equals(recvLabel));

			final ImmutableList.Builder<Loc> builder = ImmutableList.builder();
			final Loc emitSource = emitEdge.getSource();
			final Loc emitarget = emitEdge.getTarget();
			final Loc recvSource = recvEdge.getSource();
			final Loc recvTarget = recvEdge.getTarget();
			boolean emitMatched = false;
			boolean recvMatched = false;
			for (final Loc loc : sourceLocs) {
				if (loc.equals(emitSource)) {
					checkArgument(!emitMatched);
					builder.add(emitarget);
					emitMatched = true;
				} else if (loc.equals(recvSource)) {
					checkArgument(!recvMatched);
					builder.add(recvTarget);
					recvMatched = true;
				} else {
					builder.add(loc);
				}
			}
			checkArgument(emitMatched);
			checkArgument(recvMatched);
			targetLocs = builder.build();
		}

		public Edge getEmitEdge() {
			return emitEdge;
		}

		public Edge getRecvEdge() {
			return recvEdge;
		}

		@Override
		public List<Loc> getTargetLocs() {
			return targetLocs;
		}

		@Override
		public boolean isSynced() {
			return true;
		}

		@Override
		public SyncedXtaAction asSynced() {
			return this;
		}

		@Override
		public List<Stmt> getStmts() {
			List<Stmt> result = stmts;
			if (stmts == null) {
				final ImmutableList.Builder<Stmt> builder = ImmutableList.builder();
				addInvariants(builder, getSourceLocs());
				addSync(builder, emitEdge, recvEdge);
				addGuards(builder, emitEdge);
				addGuards(builder, recvEdge);
				addUpdates(builder, emitEdge);
				addUpdates(builder, recvEdge);
				addInvariants(builder, targetLocs);
				if (shouldApplyDelay(getTargetLocs())) {
					addDelay(builder, getClockVars());
				}
				result = builder.build();
				stmts = result;
			}
			return result;
		}

		@Override
		public String toString() {
			final StringJoiner sj = new StringJoiner("\n");
			sj.add(emitEdge.getSync().get().toString());
			sj.add(recvEdge.getSync().get().toString());
			emitEdge.getGuards().forEach(g -> sj.add("[" + g + "]"));
			recvEdge.getGuards().forEach(g -> sj.add("[" + g + "]"));
			emitEdge.getUpdates().forEach(u -> sj.add(u.toString()));
			recvEdge.getUpdates().forEach(u -> sj.add(u.toString()));
			return sj.toString();
		}

	}

	private static void addInvariants(final ImmutableList.Builder<Stmt> builder, final List<Loc> locs) {
		locs.forEach(l -> l.getInvars().forEach(i -> builder.add(Assume(i.toExpr()))));
	}

	private static void addSync(final Builder<Stmt> builder, final Edge emitEdge, final Edge recvEdge) {
		final Stream<Expr<?>> emitArgs = emitEdge.getSync().get().getArgs().stream();
		final Stream<Expr<?>> recvArgs = emitEdge.getSync().get().getArgs().stream();
		zip(emitArgs, recvArgs, (e, r) -> Assume(Eq(e, r))).forEach(builder::add);
	}

	private static void addGuards(final ImmutableList.Builder<Stmt> builder, final Edge edge) {
		edge.getGuards().forEach(g -> builder.add(Assume(g.toExpr())));
	}

	private static void addUpdates(final ImmutableList.Builder<Stmt> builder, final Edge edge) {
		edge.getUpdates().forEach(u -> builder.add(u.toStmt()));
	}

	private static void addDelay(final ImmutableList.Builder<Stmt> builder, final Collection<VarDecl<RatType>> clocks) {
		builder.add(Havoc(DELAY));
		builder.add(Assume(Geq(DELAY.getRef(), Rat(0, 1))));
		clocks.forEach(c -> builder.add(Assign(c, Add(c.getRef(), DELAY.getRef()))));
	}

	private static boolean shouldApplyDelay(final List<Loc> locs) {
		return locs.stream().allMatch(l -> l.getKind() == LocKind.NORMAL);
	}

}
