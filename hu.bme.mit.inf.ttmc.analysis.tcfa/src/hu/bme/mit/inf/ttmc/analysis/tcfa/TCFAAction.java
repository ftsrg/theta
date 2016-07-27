package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.ClockConstrs;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.impl.ClockOps;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public abstract class TCFAAction implements Action {

	private TCFAAction() {
	}

	public static TCFADelayAction delay(final TCFALoc loc) {
		checkNotNull(loc);
		return new TCFADelayAction(loc);
	}

	public static TCFADiscreteAction discrete(final TCFAEdge edge) {
		checkNotNull(edge);
		return new TCFADiscreteAction(edge);
	}

	private static Collection<ClockConstr> extractClockInvars(final TCFALoc loc) {
		final ImmutableSet.Builder<ClockConstr> builder = ImmutableSet.builder();
		for (final Expr<? extends BoolType> invar : loc.getInvars()) {
			if (TCFAUtils.isClockExpr(invar)) {
				builder.add(ClockConstrs.formExpr(invar));
			}
		}
		return builder.build();
	}

	public abstract Collection<ClockConstr> getSourceClockInvars();

	public abstract Collection<ClockConstr> getTargetClockInvars();

	////

	public static final class TCFADelayAction extends TCFAAction {

		private final Collection<ClockConstr> clockInvars;

		private TCFADelayAction(final TCFALoc loc) {
			assert loc != null;
			clockInvars = extractClockInvars(loc);
		}

		@Override
		public Collection<ClockConstr> getSourceClockInvars() {
			return clockInvars;
		}

		@Override
		public Collection<ClockConstr> getTargetClockInvars() {
			return clockInvars;
		}

		@Override
		public String toString() {
			final StringJoiner sj = new StringJoiner(", ", "Delay(", ")");
			for (final ClockConstr clockConstr : clockInvars) {
				sj.add(clockConstr.toExpr().toString());
			}
			return sj.toString();
		}

	}

	public static final class TCFADiscreteAction extends TCFAAction {

		private final TCFAEdge edge;

		private final Collection<ClockConstr> sourceClockInvars;
		private final Collection<Expr<? extends BoolType>> sourceDataInvars;

		private final Collection<ClockConstr> targetClockInvars;
		private final Collection<Expr<? extends BoolType>> targetDataInvars;

		private final List<ClockOp> clockOps;
		private final List<Stmt> dataStmts;

		private TCFADiscreteAction(final TCFAEdge edge) {
			this.edge = edge;
			sourceClockInvars = extractClockInvars(edge.getSource());
			sourceDataInvars = extractDataInvars(edge.getSource());
			targetClockInvars = extractClockInvars(edge.getTarget());
			targetDataInvars = extractDataInvars(edge.getTarget());

			final ImmutableList.Builder<ClockOp> clockOpsBuilder = ImmutableList.builder();
			final ImmutableList.Builder<Stmt> dataStmtsBuilder = ImmutableList.builder();

			for (final Stmt stmt : edge.getStmts()) {
				if (TCFAUtils.isClockStmt(stmt)) {
					clockOpsBuilder.add(ClockOps.fromStmt(stmt));
				} else if (TCFAUtils.isDataStmt(stmt)) {
					dataStmtsBuilder.add(stmt);
				} else {
					throw new IllegalArgumentException();
				}
			}

			clockOps = clockOpsBuilder.build();
			dataStmts = dataStmtsBuilder.build();

		}

		public TCFAEdge getEdge() {
			return edge;
		}

		@Override
		public Collection<ClockConstr> getSourceClockInvars() {
			return sourceClockInvars;
		}

		@Override
		public Collection<ClockConstr> getTargetClockInvars() {
			return targetClockInvars;
		}

		public Collection<Expr<? extends BoolType>> getSourceDataInvars() {
			return sourceDataInvars;
		}

		public Collection<Expr<? extends BoolType>> getTargetDataInvars() {
			return targetDataInvars;
		}

		public List<ClockOp> getClockOps() {
			return clockOps;
		}

		public List<Stmt> getDataStmts() {
			return dataStmts;
		}

		private static Collection<Expr<? extends BoolType>> extractDataInvars(final TCFALoc loc) {
			final ImmutableSet.Builder<Expr<? extends BoolType>> builder = ImmutableSet.builder();
			for (final Expr<? extends BoolType> invar : loc.getInvars()) {
				if (TCFAUtils.isDataExpr(invar)) {
					builder.add(invar);
				}
			}
			return builder.build();
		}

		@Override
		public String toString() {
			// TODO: should the target and source invariants also be printed?
			final StringJoiner sj = new StringJoiner(", ", "Discrete(", ")");

			for (final ClockOp clockOp : clockOps) {
				sj.add(clockOp.toString());
			}
			for (final Stmt stmt : dataStmts) {
				sj.add(stmt.toString());
			}

			return sj.toString();
		}
	}

}
