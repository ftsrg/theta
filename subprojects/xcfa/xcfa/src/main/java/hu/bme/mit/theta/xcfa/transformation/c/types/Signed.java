package hu.bme.mit.theta.xcfa.transformation.c.types;

public class Signed extends CType{
	public static Signed instance = new Signed();
	private Signed(){}

	@Override
	protected void patch(CType cType) {
		cType.setSigned(true);
	}
}
