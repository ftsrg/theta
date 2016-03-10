package hu.bme.mit.inf.ttmc.system.ui

import hu.bme.mit.inf.ttmc.constraint.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.ui.ExpressionHelper
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.formalism.common.factory.STSFactory
import hu.bme.mit.inf.ttmc.system.model.PrimedExpression
import hu.bme.mit.inf.ttmc.system.model.VariableDeclaration

class SystemExpressionHelper extends ExpressionHelper {
	
	protected val extension STSFactory stsFactory
		
	protected new(ExprFactory exprFactory, STSFactory stsFactory, DeclarationHelper declarationHelper, TypeInferrer inferrer) {
		super(exprFactory, declarationHelper, inferrer)
		this.stsFactory = stsFactory
	}
	
	////
	
	public def dispatch Expr<? extends Type> toExpr(PrimedExpression expression) {
		val op = expression.operand.toExpr
		Prime(op)
	}
	
	/////
			
	public def dispatch RefExpr<? extends Type, ?> toRefExpr(VariableDeclaration declaration) {
		val decl = declaration.toDecl
		val varDecl = decl as VarDecl<Type>
		Ref(varDecl)
	}
	
}