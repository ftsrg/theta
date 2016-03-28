package hu.bme.mit.inf.ttmc.constraint.ui.transform;

public interface TransformationManager {

	public TypeTransformator getTypeTransformator();

	public DeclTransformator getDeclTransformator();

	public ExprTransformator getExprTransformator();

}
