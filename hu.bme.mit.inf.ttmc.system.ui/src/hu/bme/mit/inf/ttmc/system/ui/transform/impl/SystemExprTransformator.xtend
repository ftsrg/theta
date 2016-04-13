package hu.bme.mit.inf.ttmc.system.ui.transform.impl

import hu.bme.mit.inf.ttmc.core.expr.Expr
import hu.bme.mit.inf.ttmc.core.type.Type
import hu.bme.mit.inf.ttmc.system.model.PrimedExpression
import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintExprTransformator


import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.*;

public class SystemExprTransformator extends ConstraintExprTransformator {
	
		
	public new(SystemTransformationManager manager) {
		super(manager)
	}
	
	////
	
	protected def dispatch Expr<? extends Type> toExpr(PrimedExpression expression) {
		val op = expression.operand.toExpr
		Prime(op)
	}

	
}