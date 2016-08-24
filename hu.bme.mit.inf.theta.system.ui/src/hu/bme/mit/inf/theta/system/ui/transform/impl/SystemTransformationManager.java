package hu.bme.mit.inf.theta.system.ui.transform.impl;

import hu.bme.mit.inf.theta.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.theta.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.theta.constraint.ui.transform.TransformationManager;
import hu.bme.mit.inf.theta.constraint.ui.transform.TypeTransformator;
import hu.bme.mit.inf.theta.constraint.ui.transform.impl.ConstraintTypeTransformator;
import hu.bme.mit.inf.theta.system.ui.transform.impl.SystemDeclTransformator;
import hu.bme.mit.inf.theta.system.ui.transform.impl.SystemExprTransformator;

public class SystemTransformationManager implements TransformationManager {

	private final TypeTransformator typeTransformator;
	private final DeclTransformator declTransformator;
	private final ExprTransformator exprTransformator;

	public SystemTransformationManager() {
		typeTransformator = new ConstraintTypeTransformator(this);
		declTransformator = new SystemDeclTransformator(this);
		exprTransformator = new SystemExprTransformator(this);
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
