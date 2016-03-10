package hu.bme.mit.inf.ttmc.program.ui

import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.ui.ExpressionHelper
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer
import hu.bme.mit.inf.ttmc.formalism.common.factory.ProgramFactory

class ProgramExpressionHelper extends ExpressionHelper {
	
	private val extension ProgramFactory programFactory
		
	new(ExprFactory exprFactory, ProgramFactory programFactory, DeclarationHelper declarationHelper, TypeInferrer typeInferrer) {
		super(exprFactory, declarationHelper, typeInferrer)
		this.programFactory = programFactory
	}
	
	////////
	
}