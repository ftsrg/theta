package hu.bme.mit.theta.frontend.transformation.model.types.simple;

public class Typedef extends CSimpleType {
	public static Typedef instance = new Typedef();
	private Typedef(){}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		cSimpleType.setTypedef(true);
	}
}
