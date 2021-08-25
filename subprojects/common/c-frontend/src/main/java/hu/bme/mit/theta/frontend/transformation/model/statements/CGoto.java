package hu.bme.mit.theta.frontend.transformation.model.statements;

public class CGoto extends CStatement{
	private final String label;

	public CGoto(String id) {
		this.label = id;
	}

	public String getLabel() {
		return label;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
