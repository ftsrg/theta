package hu.bme.mit.theta.xcfa.transformation.c.types;

public class Atomic extends CType{
	public static Atomic instance = new Atomic();
	private Atomic(){}

	@Override
	protected void patch(CType cType) {
		cType.setAtomic(true);
	}
}
