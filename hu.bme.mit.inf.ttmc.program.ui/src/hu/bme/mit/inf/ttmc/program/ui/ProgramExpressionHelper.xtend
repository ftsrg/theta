package hu.bme.mit.inf.ttmc.program.ui

import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.ui.ExpressionHelper
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.formalism.common.factory.ProgramFactory
import hu.bme.mit.inf.ttmc.program.model.VariableDeclaration

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