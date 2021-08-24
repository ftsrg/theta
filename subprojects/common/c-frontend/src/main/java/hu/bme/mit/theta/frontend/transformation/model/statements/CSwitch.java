package hu.bme.mit.theta.frontend.transformation.model.statements;

public class CSwitch extends CStatement{
	private final CStatement testValue;
	private final CStatement body;

	public CSwitch(CStatement testValue, CStatement body) {
		this.testValue = testValue;
		this.body = body;
	}

	public CStatement getBody() {
		return body;
	}

	public CStatement getTestValue() {
		return testValue;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
