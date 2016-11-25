package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Add;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Prime;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Rat;
import static hu.bme.mit.theta.core.type.impl.Types.Rat;
import static hu.bme.mit.theta.core.utils.impl.VarIndexing.all;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.loc.LocAction;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.core.utils.impl.StmtUtils;
import hu.bme.mit.theta.core.utils.impl.UnfoldResult;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaAction implements LocAction<TcfaLoc, TcfaEdge> {

	private static final VarDecl<RatType> DELAY_VAR = Var("_delay", Rat());

	private final TcfaEdge edge;

	private final Collection<TcfaExpr> sourceInvars;
	private final Collection<TcfaExpr> targetInvars;
	private final List<TcfaStmt> tcfaStmts;

	private final Expr<? extends BoolType> expr;
	private final VarIndexing nextIndexing;

	private TcfaAction(final TCFA tcfa, final TcfaEdge edge) {
		checkNotNull(tcfa);
		checkNotNull(edge);
		// checkArgument(tcfa.getEdges().contains(edge));

		this.edge = edge;

		sourceInvars = invarsOf(edge.getSource());
		targetInvars = invarsOf(edge.getTarget());
		tcfaStmts = ImmutableList.copyOf(edge.getStmts().stream().map(TcfaStmt::of).collect(toList()));

		final UnfoldResult unfoldResult = unfold(tcfa, edge);
		expr = And(unfoldResult.getExprs());
		nextIndexing = unfoldResult.getIndexing();
	}

	public static TcfaAction create(final TCFA tcfa, final TcfaEdge edge) {
		return new TcfaAction(tcfa, edge);
	}

	public static VarDecl<RatType> getDelayVar() {
		return DELAY_VAR;
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
		return expr;
	}

	@Override
	public VarIndexing nextIndexing() {
		return nextIndexing;
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

	private static final UnfoldResult unfold(final TCFA tcfa, final TcfaEdge edge) {
		final List<Expr<? extends BoolType>> exprs = new ArrayList<>();

		VarIndexing indexing = all(0);

		for (final Expr<? extends BoolType> invar : edge.getSource().getInvars()) {
			exprs.add(invar);
		}

		if (!edge.getSource().isUrgent()) {
			final Expr<RatType> primedDelay = Prime(DELAY_VAR.getRef());

			exprs.add(Geq(primedDelay, Rat(0, 1)));
			indexing = indexing.inc(DELAY_VAR);

			for (final ClockDecl clockDecl : tcfa.getClockVars()) {
				final Expr<RatType> clock = clockDecl.getRef();
				final Expr<RatType> primedClock = Prime(clock);
				exprs.add(Eq(primedClock, Add(clock, primedDelay)));
				indexing = indexing.inc(clockDecl);
			}

			for (final Expr<? extends BoolType> invar : edge.getSource().getInvars()) {
				exprs.add(ExprUtils.applyPrimes(invar, indexing));
			}
		}

		final UnfoldResult stmtToExprResult = StmtUtils.toExpr(edge.getStmts(), indexing);

		exprs.addAll(stmtToExprResult.getExprs());
		indexing = stmtToExprResult.getIndexing();

		for (final Expr<? extends BoolType> invar : edge.getTarget().getInvars()) {
			exprs.add(ExprUtils.applyPrimes(invar, all(1)));
		}

		return UnfoldResult.of(exprs, indexing);
	}

}
