package hu.bme.mit.theta.xcfa.transformation.model.types.simple;

public class Signed extends CSimpleType {
	public static Signed instance = new Signed();
	private Signed(){}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		cSimpleType.setSigned(true);
	}
}
