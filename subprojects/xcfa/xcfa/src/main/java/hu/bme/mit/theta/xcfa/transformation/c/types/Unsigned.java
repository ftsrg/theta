package hu.bme.mit.theta.xcfa.transformation.c.types;

public class Unsigned extends CType{
	public static Unsigned instance = new Unsigned();
	private Unsigned(){}

	@Override
	protected void patch(CType cType) {
		cType.setSigned(false);
	}
}
