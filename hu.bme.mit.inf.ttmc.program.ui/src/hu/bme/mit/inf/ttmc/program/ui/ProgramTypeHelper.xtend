package hu.bme.mit.inf.ttmc.program.ui

import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory
import hu.bme.mit.inf.ttmc.constraint.ui.TypeHelper
import hu.bme.mit.inf.ttmc.formalism.common.factory.ProgramFactory

class ProgramTypeHelper extends TypeHelper {
	
	protected val extension ProgramFactory programFactory
	
	new(TypeFactory typeFactory, ProgramFactory programFactory) {
		super(typeFactory)
		this.programFactory = programFactory
	}
	
}