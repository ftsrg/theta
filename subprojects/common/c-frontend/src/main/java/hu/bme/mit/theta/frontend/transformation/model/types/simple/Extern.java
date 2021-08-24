package hu.bme.mit.theta.frontend.transformation.model.types.simple;

public class Extern extends CSimpleType {
	public static Extern instance = new Extern();
	private Extern(){}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		cSimpleType.setExtern(true);
	}
}
