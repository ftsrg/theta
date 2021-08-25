package hu.bme.mit.theta.frontend.transformation.model.statements;

public class CCase extends CStatement{
	private final CStatement expr;
	private final CStatement statement;

	public CCase(CStatement expr, CStatement statement) {
		this.expr = expr;
		this.statement = statement;
	}

	public CStatement getExpr() {
		return expr;
	}

	public CStatement getStatement() {
		return statement;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
