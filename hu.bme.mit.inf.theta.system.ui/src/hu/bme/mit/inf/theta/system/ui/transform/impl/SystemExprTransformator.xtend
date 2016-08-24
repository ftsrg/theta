package hu.bme.mit.inf.theta.system.ui.transform.impl

import hu.bme.mit.inf.theta.constraint.ui.transform.impl.ConstraintExprTransformator
import hu.bme.mit.inf.theta.core.expr.Expr
import hu.bme.mit.inf.theta.core.type.Type
import hu.bme.mit.inf.theta.system.model.PrimedExpression

import static hu.bme.mit.inf.theta.formalism.common.expr.impl.Exprs2.*

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