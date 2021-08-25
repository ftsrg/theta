package hu.bme.mit.theta.frontend.transformation.model.statements;

public class CContinue extends CStatement{
	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
