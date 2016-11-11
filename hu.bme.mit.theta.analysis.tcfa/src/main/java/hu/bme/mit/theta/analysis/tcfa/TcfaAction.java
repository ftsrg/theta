package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.loc.LocAction;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaAction implements LocAction<TcfaLoc, TcfaEdge> {

	private final TcfaEdge edge;

	private final Collection<TcfaExpr> sourceInvars;
	private final Collection<TcfaExpr> targetInvars;
	private final List<TcfaStmt> tcfaStmts;

	private TcfaAction(final TcfaEdge edge) {
		this.edge = checkNotNull(edge);
		sourceInvars = invarsOf(edge.getSource());
		targetInvars = invarsOf(edge.getTarget());
		tcfaStmts = ImmutableList.copyOf(edge.getStmts().stream().map(TcfaStmt::of).collect(toList()));
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

	public List<TcfaStmt> getTcfaStmts() {
		return tcfaStmts;
	}

	////

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public VarIndexing nextIndexing() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("TcfaAction").addAll(tcfaStmts).toString();
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
