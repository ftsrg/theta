package hu.bme.mit.inf.theta.constraint.ui.transform;

public interface TransformationManager {

	public TypeTransformator getTypeTransformator();

	public DeclTransformator getDeclTransformator();

	public ExprTransformator getExprTransformator();

}
