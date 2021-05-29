package hu.bme.mit.theta.xcfa.transformation.c.types;

public class Extern extends CType{
	public static Extern instance = new Extern();
	private Extern(){}

	@Override
	protected void patch(CType cType) {
		cType.setExtern(true);
	}
}
