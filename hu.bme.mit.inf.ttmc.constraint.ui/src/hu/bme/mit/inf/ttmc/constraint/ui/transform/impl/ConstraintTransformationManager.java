package hu.bme.mit.inf.ttmc.constraint.ui.transform.impl;

import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TypeTransformator;

public class ConstraintTransformationManager implements TransformationManager {

	private final TypeTransformator typeTransformator;
	private final DeclTransformator declTransformator;
	private final ExprTransformator exprTransformator;

	public ConstraintTransformationManager() {
		typeTransformator = new ConstraintTypeTransformator(this);
		declTransformator = new ConstraintDeclTransformator(this);
		exprTransformator = new ConstraintExprTransformator(this);
	}

	@Override
	public TypeTransformator getTypeTransformator() {
		return typeTransformator;
	}

	@Override
	public DeclTransformator getDeclTransformator() {
		return declTransformator;
	}

	@Override
	public ExprTransformator getExprTransformator() {
		return exprTransformator;
	}

}
