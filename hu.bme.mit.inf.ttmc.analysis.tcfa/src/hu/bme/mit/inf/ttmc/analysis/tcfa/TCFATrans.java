package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.ClockConstrs;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.impl.ClockOps;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public abstract class TCFATrans {

	private TCFATrans() {
	}

	public static TCFADelayTrans delay(final TCFALoc loc) {
		checkNotNull(loc);
		return new TCFADelayTrans(loc);
	}

	public static TCFADiscreteTrans discrete(final TCFAEdge edge) {
		checkNotNull(edge);
		return new TCFADiscreteTrans(edge);
	}

	private static Collection<ClockConstr> extractClockInvars(
			final Collection<? extends Expr<? extends BoolType>> invars) {
		final ImmutableSet.Builder<ClockConstr> builder = ImmutableSet.builder();
		for (final Expr<? extends BoolType> invar : invars) {
			if (TCFAUtils.isClockExpr(invar)) {
				builder.add(ClockConstrs.formExpr(invar));
			}
		}
		return builder.build();
	}

	public abstract Collection<ClockConstr> getClockInvars();

	////

	public static final class TCFADelayTrans extends TCFATrans {

		private final Collection<ClockConstr> clockInvars;

		private TCFADelayTrans(final TCFALoc loc) {
			assert loc != null;
			clockInvars = extractClockInvars(loc.getInvars());
		}

		@Override
		public Collection<ClockConstr> getClockInvars() {
			return clockInvars;
		}

	}

	public static final class TCFADiscreteTrans extends TCFATrans {

		private final TCFAEdge edge;
		private final Collection<ClockConstr> clockInvars;
		private final Collection<Expr<? extends BoolType>> dataInvars;
		private final List<ClockOp> clockOps;
		private final List<Stmt> dataStmts;

		private TCFADiscreteTrans(final TCFAEdge edge) {
			assert edge != null;

			this.edge = edge;
			clockInvars = extractClockInvars(edge.getTarget().getInvars());
			dataInvars = extractDataInvars(edge.getTarget().getInvars());
			clockOps = extractClockOps(edge.getStmts());
			dataStmts = extractDataStmts(edge.getStmts());
		}

		public TCFAEdge getEdge() {
			return edge;
		}

		@Override
		public Collection<ClockConstr> getClockInvars() {
			return clockInvars;
		}

		public Collection<Expr<? extends BoolType>> getDataInvars() {
			return dataInvars;
		}

		public List<ClockOp> getClockOps() {
			return clockOps;
		}

		public List<Stmt> getDataStmts() {
			return dataStmts;
		}

		private static Collection<Expr<? extends BoolType>> extractDataInvars(
				final Collection<? extends Expr<? extends BoolType>> invars) {
			final ImmutableSet.Builder<Expr<? extends BoolType>> builder = ImmutableSet.builder();
			for (final Expr<? extends BoolType> invar : invars) {
				if (TCFAUtils.isDataExpr(invar)) {
					builder.add(invar);
				}
			}
			return builder.build();
		}

		private static List<ClockOp> extractClockOps(final Collection<? extends Stmt> stmts) {
			final ImmutableList.Builder<ClockOp> builder = ImmutableList.builder();
			for (final Stmt stmt : stmts) {
				if (TCFAUtils.isClockStmt(stmt)) {
					builder.add(ClockOps.fromStmt(stmt));
				}
			}
			return builder.build();
		}

		private static List<Stmt> extractDataStmts(final Collection<? extends Stmt> stmts) {
			final ImmutableList.Builder<Stmt> builder = ImmutableList.builder();
			for (final Stmt stmt : stmts) {
				if (TCFAUtils.isDataStmt(stmt)) {
					builder.add(stmt);
				}
			}
			return builder.build();
		}

	}

}
