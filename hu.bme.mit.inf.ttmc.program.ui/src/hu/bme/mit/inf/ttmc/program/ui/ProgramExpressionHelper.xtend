package hu.bme.mit.inf.ttmc.program.ui

import hu.bme.mit.inf.ttmc.constraint.ui.ExpressionHelper
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer
import hu.bme.mit.inf.ttmc.formalism.factory.ProgramFactory
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl
import hu.bme.mit.inf.ttmc.program.model.VariableDeclaration
import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr
import hu.bme.mit.inf.ttmc.constraint.type.Type

class ProgramExpressionHelper extends ExpressionHelper {
	
	private val extension ProgramFactory programFactory
		
	new(ExprFactory exprFactory, ProgramFactory programFactory, DeclarationHelper declarationHelper, TypeInferrer typeInferrer) {
		super(exprFactory, declarationHelper, typeInferrer)
		this.programFactory = programFactory
	}
	
	////////
	
	public def dispatch RefExpr<? extends Type, ?> toRefExpr(VariableDeclaration declaration) {
		val decl = declaration.toDecl
		val varDecl = decl as VarDecl<Type>
		Ref(varDecl)
	}
	
}