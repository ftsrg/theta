package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.utils.impl.VarIndexes.all;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.StmtUnroller;
import hu.bme.mit.theta.core.utils.impl.StmtUnroller.StmtToExprResult;
import hu.bme.mit.theta.core.utils.impl.VarIndexes;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;

public final class CfaAction implements ExprAction {

	private final CfaEdge edge;
	private final Expr<? extends BoolType> expr;
	private final VarIndexes nextIndexes;

	private CfaAction(final CfaEdge edge) {
		this.edge = checkNotNull(edge);

		final StmtToExprResult toExprResult = StmtUnroller.transform(edge.getStmts(), all(0));
		expr = And(toExprResult.getExprs());
		nextIndexes = toExprResult.getIndexes();
	}

	public CfaEdge getEdge() {
		return edge;
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		return expr;
	}

	@Override
	public VarIndexes nextIndexes() {
		return nextIndexes;
	}

}
