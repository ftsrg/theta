package hu.bme.mit.inf.ttmc.program.ui.transform.impl

import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintExprTransformator
import hu.bme.mit.inf.ttmc.core.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.model.ReferenceExpression
import hu.bme.mit.inf.ttmc.program.model.VariableDeclaration

import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.*;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.core.type.Type
import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator

class ProgramExprTransformator extends ConstraintExprTransformator {
	
	private val ProgramTransformationManager manager
	
	private volatile DeclTransformator dt
	
	new(ProgramTransformationManager manager) {
		super(manager)
		this.manager = manager;
	}
	
	private def DeclTransformator getDeclTransformator() {
		if (dt === null) {
			dt = manager.declTransformator
		}
		dt
	}
	
	protected def dispatch Expr<? extends Type> toRefExpr(ReferenceExpression expression, VariableDeclaration declaration) {
		val decl = declTransformator.transform(expression.declaration) as VarDecl<? extends Type>
		Ref(decl)
	}
	
}