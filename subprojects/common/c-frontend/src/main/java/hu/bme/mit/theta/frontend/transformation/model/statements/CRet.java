package hu.bme.mit.theta.frontend.transformation.model.statements;

public class CRet extends CStatement{
	private final CStatement expr;

	public CRet(CStatement expr) {
		this.expr = expr;
	}

	public CStatement getExpr() {
		return expr;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
