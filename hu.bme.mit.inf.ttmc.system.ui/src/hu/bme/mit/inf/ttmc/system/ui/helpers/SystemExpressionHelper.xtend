package hu.bme.mit.inf.ttmc.system.ui.helpers

import hu.bme.mit.inf.ttmc.constraint.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory
import hu.bme.mit.inf.ttmc.system.model.PrimedExpression
import hu.bme.mit.inf.ttmc.constraint.ui.helpers.ExpressionHelper

public class SystemExpressionHelper extends ExpressionHelper {
	
	private val extension STSExprFactory stsExprFactory;
		
	public new(STSExprFactory exprFactory, SystemDeclarationHelper declarationHelper) {
		super(exprFactory, declarationHelper)
		this.stsExprFactory = exprFactory
	}
	
	////
	
	public def dispatch Expr<? extends Type> toExpr(PrimedExpression expression) {
		val op = expression.operand.toExpr
		Prime(op)
	}

	
}