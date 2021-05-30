package hu.bme.mit.theta.xcfa.transformation.c.statements;

public class CGoto extends CStatement{
	private final String id;

	public CGoto(String id) {
		this.id = id;
	}

	public String getFunctionId() {
		return id;
	}
}
