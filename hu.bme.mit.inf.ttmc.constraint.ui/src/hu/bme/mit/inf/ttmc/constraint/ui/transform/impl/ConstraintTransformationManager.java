package hu.bme.mit.inf.ttmc.constraint.ui.transform.impl;

import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TypeTransformator;
import hu.bme.mit.inf.ttmc.core.ConstraintManager;

public class ConstraintTransformationManager implements TransformationManager {

	private final TypeTransformator typeTransformator;
	private final DeclTransformator declTransformator;
	private final ExprTransformator exprTransformator;

	public ConstraintTransformationManager(final ConstraintManager manager) {
		typeTransformator = new ConstraintTypeTransformator(this, manager.getTypeFactory());
		declTransformator = new ConstraintDeclTransformator(this, manager.getDeclFactory());
		exprTransformator = new ConstraintExprTransformator(this, manager.getExprFactory());
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
