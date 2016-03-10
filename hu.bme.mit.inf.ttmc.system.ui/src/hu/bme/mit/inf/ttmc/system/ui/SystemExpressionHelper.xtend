package hu.bme.mit.inf.ttmc.system.ui

import hu.bme.mit.inf.ttmc.constraint.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.ui.ExpressionHelper
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer
import hu.bme.mit.inf.ttmc.system.model.PrimedExpression
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory

class SystemExpressionHelper extends ExpressionHelper {
	
	private val extension STSExprFactory stsExprFactory;
		
	protected new(STSExprFactory exprFactory, DeclarationHelper declarationHelper, TypeInferrer inferrer) {
		super(exprFactory, declarationHelper, inferrer)
		this.stsExprFactory = exprFactory
	}
	
	////
	
	public def dispatch Expr<? extends Type> toExpr(PrimedExpression expression) {
		val op = expression.operand.toExpr
		Prime(op)
	}

	
}