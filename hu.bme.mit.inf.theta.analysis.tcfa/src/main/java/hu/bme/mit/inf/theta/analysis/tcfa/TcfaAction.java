package hu.bme.mit.inf.theta.analysis.tcfa;

import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.theta.analysis.Action;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.theta.formalism.ta.constr.impl.ClockConstrs;
import hu.bme.mit.inf.theta.formalism.ta.op.ClockOp;
import hu.bme.mit.inf.theta.formalism.ta.op.impl.ClockOps;
import hu.bme.mit.inf.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.inf.theta.formalism.tcfa.TcfaLoc;

public final class TcfaAction implements Action {

	private final TcfaEdge edge;

	private final Collection<ClockConstr> sourceClockInvars;
	private final Collection<Expr<? extends BoolType>> sourceDataInvars;

	private final Collection<ClockConstr> targetClockInvars;
	private final Collection<Expr<? extends BoolType>> targetDataInvars;

	private final List<ClockOp> clockOps;
	private final List<Stmt> dataStmts;

	TcfaAction(final TcfaEdge edge) {
		this.edge = edge;
		sourceClockInvars = extractClockInvars(edge.getSource());
		sourceDataInvars = extractDataInvars(edge.getSource());
		targetClockInvars = extractClockInvars(edge.getTarget());
		targetDataInvars = extractDataInvars(edge.getTarget());

		final ImmutableList.Builder<ClockOp> clockOpsBuilder = ImmutableList.builder();
		final ImmutableList.Builder<Stmt> dataStmtsBuilder = ImmutableList.builder();

		for (final Stmt stmt : edge.getStmts()) {
			if (TcfaUtils.isClockStmt(stmt)) {
				clockOpsBuilder.add(ClockOps.fromStmt(stmt));
			} else if (TcfaUtils.isDataStmt(stmt)) {
				dataStmtsBuilder.add(stmt);
			} else {
				throw new IllegalArgumentException();
			}
		}

		clockOps = clockOpsBuilder.build();
		dataStmts = dataStmtsBuilder.build();

	}

	public TcfaEdge getEdge() {
		return edge;
	}

	public Collection<ClockConstr> getSourceClockInvars() {
		return sourceClockInvars;
	}

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

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "TCFAAction(", ")");

		for (final ClockOp clockOp : clockOps) {
			sj.add(clockOp.toString());
		}
		for (final Stmt stmt : dataStmts) {
			sj.add(stmt.toString());
		}

		return sj.toString();
	}

	private static Collection<Expr<? extends BoolType>> extractDataInvars(final TcfaLoc loc) {
		final ImmutableSet.Builder<Expr<? extends BoolType>> builder = ImmutableSet.builder();
		for (final Expr<? extends BoolType> invar : loc.getInvars()) {
			if (TcfaUtils.isDataExpr(invar)) {
				builder.add(invar);
			}
		}
		return builder.build();
	}

	private static Collection<ClockConstr> extractClockInvars(final TcfaLoc loc) {
		final ImmutableSet.Builder<ClockConstr> builder = ImmutableSet.builder();
		for (final Expr<? extends BoolType> invar : loc.getInvars()) {
			if (TcfaUtils.isClockExpr(invar)) {
				builder.add(ClockConstrs.formExpr(invar));
			}
		}
		return builder.build();
	}

}
