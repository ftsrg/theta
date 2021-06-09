package hu.bme.mit.theta.xcfa.transformation.c.types;

public class Volatile extends CType{
	public static Volatile instance = new Volatile();
	private Volatile(){}

	@Override
	protected void patch(CType cType) {
		cType.setVolatile(true);
	}
}
