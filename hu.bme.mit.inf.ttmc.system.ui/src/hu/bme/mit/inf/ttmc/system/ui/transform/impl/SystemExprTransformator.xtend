package hu.bme.mit.inf.ttmc.system.ui.transform.impl

import hu.bme.mit.inf.ttmc.core.expr.Expr
import hu.bme.mit.inf.ttmc.core.type.Type
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory
import hu.bme.mit.inf.ttmc.system.model.PrimedExpression
import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintExprTransformator

public class SystemExprTransformator extends ConstraintExprTransformator {
	
	private val extension STSExprFactory stsExprFactory;
		
	public new(SystemTransformationManager manager, STSExprFactory exprFactory) {
		super(manager, exprFactory)
		this.stsExprFactory = exprFactory
	}
	
	////
	
	protected def dispatch Expr<? extends Type> toExpr(PrimedExpression expression) {
		val op = expression.operand.toExpr
		Prime(op)
	}

	
}