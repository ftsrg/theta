package hu.bme.mit.theta.frontend.transformation.model.types.simple;

public class Volatile extends CSimpleType {
	public static Volatile instance = new Volatile();
	private Volatile(){}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		cSimpleType.setVolatile(true);
	}
}
