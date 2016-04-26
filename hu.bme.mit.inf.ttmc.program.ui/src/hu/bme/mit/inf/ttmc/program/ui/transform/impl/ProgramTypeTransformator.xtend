package hu.bme.mit.inf.ttmc.program.ui.transform.impl

import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager
import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintTypeTransformator
import hu.bme.mit.inf.ttmc.formalism.common.type.UnitType
import hu.bme.mit.inf.ttmc.program.model.UnitTypeDefinition

import static hu.bme.mit.inf.ttmc.formalism.common.type.impl.Types2.Unit;

class ProgramTypeTransformator extends ConstraintTypeTransformator {
	
	new(TransformationManager manager) {
		super(manager)
	}
	
	public def dispatch UnitType toType(UnitTypeDefinition type) {
		Unit
	}

	
}