package hu.bme.mit.theta.frontend.transformation.model.types.simple;

public class Unsigned extends CSimpleType {
	public static Unsigned instance = new Unsigned();
	private Unsigned(){}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		cSimpleType.setSigned(false);
	}
}
