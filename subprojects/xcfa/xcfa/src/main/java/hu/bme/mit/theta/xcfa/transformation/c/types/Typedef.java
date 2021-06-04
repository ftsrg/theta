package hu.bme.mit.theta.xcfa.transformation.c.types;

public class Typedef extends CType{
	public static Typedef instance = new Typedef();
	private Typedef(){}

	@Override
	protected void patch(CType cType) {
		cType.setTypedef(true);
	}
}
