package hu.bme.mit.theta.xcfa.transformation.c.types;

public class DeclaredName extends CType{
	private String declaredName;
	DeclaredName(String declaredName){ this.declaredName = declaredName; }

	@Override
	protected void patch(CType cType) {
		cType.setAssociatedName(declaredName);
	}
}
