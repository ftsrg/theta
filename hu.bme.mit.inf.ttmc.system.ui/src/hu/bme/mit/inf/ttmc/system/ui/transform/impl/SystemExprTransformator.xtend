package hu.bme.mit.inf.ttmc.system.ui.transform.impl

import hu.bme.mit.inf.ttmc.core.expr.Expr
import hu.bme.mit.inf.ttmc.core.type.Type
import hu.bme.mit.inf.ttmc.system.model.PrimedExpression
import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintExprTransformator


import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.*;
import hu.bme.mit.inf.ttmc.constraint.model.ReferenceExpression
import hu.bme.mit.inf.ttmc.system.model.VariableDeclaration
import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl

public class SystemExprTransformator extends ConstraintExprTransformator {
	
	private val SystemTransformationManager manager
	
	private volatile DeclTransformator dt
		
		
	public new(SystemTransformationManager manager) {
		super(manager)
		this.manager = manager;
	}
	
	private def DeclTransformator getDeclTransformator() {
		if (dt === null) {
			dt = manager.declTransformator
		}
		dt
	}
	
	////
	
	protected def dispatch Expr<? extends Type> toExpr(PrimedExpression expression) {
		val op = expression.operand.toExpr
		Prime(op)
	}
	
	protected def dispatch Expr<? extends Type> toRefExpr(ReferenceExpression expression, VariableDeclaration declaration) {
		val decl = declTransformator.transform(expression.declaration) as VarDecl<? extends Type>
		Ref(decl)
	}

	
}