package hu.bme.mit.inf.ttmc.system.ui.transform.impl;

import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TypeTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintTypeTransformator;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

public class SystemTransformationManager implements TransformationManager {

	private final TypeTransformator typeTransformator;
	private final DeclTransformator declTransformator;
	private final ExprTransformator exprTransformator;

	public SystemTransformationManager(final STSManager manager) {
		typeTransformator = new ConstraintTypeTransformator(this, manager.getTypeFactory());
		declTransformator = new SystemDeclTransformator(this, manager.getDeclFactory());
		exprTransformator = new SystemExprTransformator(this, manager.getExprFactory());
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
