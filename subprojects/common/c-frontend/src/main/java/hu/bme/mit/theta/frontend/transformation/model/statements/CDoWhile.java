package hu.bme.mit.theta.frontend.transformation.model.statements;

public class CDoWhile extends CStatement{
	private final CStatement body;
	private final CStatement guard;

	public CDoWhile(CStatement body, CStatement guard) {
		this.body = body;
		this.guard = guard;
	}

	public CStatement getBody() {
		return body;
	}

	public CStatement getGuard() {
		return guard;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
