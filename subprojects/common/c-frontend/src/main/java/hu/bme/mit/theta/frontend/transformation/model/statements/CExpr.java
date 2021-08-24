package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.type.Expr;

public class CExpr extends CStatement{
	private final Expr<?> expr;

	public CExpr(Expr<?> expr) {
		this.expr = expr;
	}

	public Expr<?> getExpr() {
		return expr;
	}

	@Override
	public Expr<?> getExpression() {
		return expr;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
