package hu.bme.mit.theta.frontend.transformation.model.statements;

public class CDefault extends CStatement{
	private final CStatement statement;

	public CDefault(CStatement statement) {
		this.statement = statement;
	}

	public CStatement getStatement() {
		return statement;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
