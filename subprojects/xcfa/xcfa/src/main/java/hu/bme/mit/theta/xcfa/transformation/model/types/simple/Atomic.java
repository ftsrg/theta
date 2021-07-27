package hu.bme.mit.theta.xcfa.transformation.model.types.simple;

public class Atomic extends CSimpleType {
	public static Atomic instance = new Atomic();
	private Atomic(){}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		cSimpleType.setAtomic(true);
	}
}
