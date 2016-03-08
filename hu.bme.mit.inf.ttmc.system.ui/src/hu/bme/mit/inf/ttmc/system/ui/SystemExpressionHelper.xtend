package hu.bme.mit.inf.ttmc.system.ui

import hu.bme.mit.inf.ttmc.constraint.ui.ExpressionHelper
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer
import hu.bme.mit.inf.ttmc.formalism.factory.ProgramFactory
import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr
import hu.bme.mit.inf.ttmc.system.model.PrimedExpression
import hu.bme.mit.inf.ttmc.system.model.VariableDeclaration
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl
import hu.bme.mit.inf.ttmc.constraint.expr.Expr

class SystemExpressionHelper extends ExpressionHelper {
	
	protected val extension ProgramFactory programFactory
		
	protected new(ExprFactory exprFactory, ProgramFactory programFactory, DeclarationHelper declarationHelper, TypeInferrer inferrer) {
		super(exprFactory, declarationHelper, inferrer)
		this.programFactory = programFactory
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