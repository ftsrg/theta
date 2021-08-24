package hu.bme.mit.theta.frontend.transformation.model.statements;

public class CIf extends CStatement{
	private final CStatement guard;
	private final CStatement body;
	private final CStatement elseStatement;

	public CIf(CStatement guard, CStatement body, CStatement elseStatement) {
		this.guard = guard;
		this.body = body;
		this.elseStatement = elseStatement;
	}

	public CStatement getElseStatement() {
		return elseStatement;
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
