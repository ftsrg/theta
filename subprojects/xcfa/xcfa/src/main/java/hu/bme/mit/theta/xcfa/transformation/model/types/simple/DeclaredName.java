package hu.bme.mit.theta.xcfa.transformation.model.types.simple;

public class DeclaredName extends CSimpleType {
	private String declaredName;
	DeclaredName(String declaredName){ this.declaredName = declaredName; }

	@Override
	protected void patch(CSimpleType cSimpleType) {
		cSimpleType.setAssociatedName(declaredName);
	}
}
