package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.loc.LocAction;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.formalism.ta.op.ClockOp;
import hu.bme.mit.theta.formalism.ta.op.impl.ClockOps;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaAction implements LocAction<TcfaLoc, TcfaEdge> {

	private final TcfaEdge edge;

	private final Collection<TcfaExpr> sourceInvars;
	private final Collection<TcfaExpr> targetInvars;

	private final List<ClockOp> clockOps;
	private final List<Stmt> dataStmts;

	private TcfaAction(final TcfaEdge edge) {
		this.edge = checkNotNull(edge);
		sourceInvars = invarsOf(edge.getSource());
		targetInvars = invarsOf(edge.getTarget());

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

	public static TcfaAction create(final TcfaEdge edge) {
		return new TcfaAction(edge);
	}

	@Override
	public TcfaEdge getEdge() {
		return edge;
	}

	public Collection<TcfaExpr> getSourceInvars() {
		return sourceInvars;
	}

	public Collection<TcfaExpr> getTargetInvars() {
		return targetInvars;
	}

	public List<ClockOp> getClockOps() {
		return clockOps;
	}

	public List<Stmt> getDataStmts() {
		return dataStmts;
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	@Override
	public VarIndexing nextIndexing() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("TcfaAction").addAll(clockOps).addAll(dataStmts).toString();
	}

	////

	private static Collection<TcfaExpr> invarsOf(final TcfaLoc loc) {
		final ImmutableSet.Builder<TcfaExpr> builder = ImmutableSet.builder();
		for (final Expr<? extends BoolType> expr : loc.getInvars()) {
			final TcfaExpr invar = TcfaExpr.of(expr);
			builder.add(invar);
		}
		return builder.build();
	}

}
