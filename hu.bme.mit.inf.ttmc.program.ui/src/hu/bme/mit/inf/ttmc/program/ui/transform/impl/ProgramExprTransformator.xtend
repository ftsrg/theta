package hu.bme.mit.inf.ttmc.program.ui.transform.impl

import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintExprTransformator
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory

class ProgramExprTransformator extends ConstraintExprTransformator {
	
	new(TransformationManager manager, ExprFactory exprFactory) {
		super(manager, exprFactory)
	}
	
}