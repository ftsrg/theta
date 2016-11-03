package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.utils.impl.VarIndexing.all;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.loc.LocAction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.StmtToExprResult;
import hu.bme.mit.theta.core.utils.impl.StmtUtils;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;

public final class CfaAction implements LocAction<CfaLoc, CfaEdge>, ExprAction {

	private final CfaEdge edge;
	private final Expr<? extends BoolType> expr;
	private final VarIndexing nextIndexing;

	private CfaAction(final CfaEdge edge) {
		this.edge = checkNotNull(edge);

		final StmtToExprResult toExprResult = StmtUtils.toExpr(edge.getStmts(), all(0));
		expr = And(toExprResult.getExprs());
		nextIndexing = toExprResult.getIndexing();
	}

	public static CfaAction create(final CfaEdge edge) {
		return new CfaAction(edge);
	}

	@Override
	public CfaEdge getEdge() {
		return edge;
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		return expr;
	}

	@Override
	public VarIndexing nextIndexing() {
		return nextIndexing;
	}

}
