package hu.bme.mit.inf.ttmc.constraint.ui.transform.impl

import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.model.TypeReference
import hu.bme.mit.inf.ttmc.constraint.model.BooleanTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.IntegerTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.RealTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.FunctionTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.ArrayTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TypeTransformator
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager

public class ConstraintTypeTransformator implements TypeTransformator {

	private val TransformationManager manager
	
	private val extension TypeFactory typeFactory

	public new(TransformationManager manager, TypeFactory typeFactory) {
		this.manager = manager
		this.typeFactory = typeFactory
	}
	
	///////
		
	override transform(hu.bme.mit.inf.ttmc.constraint.model.Type type) {
		return type.toType
	}

	///////
	
	public def dispatch Type toType(hu.bme.mit.inf.ttmc.constraint.model.Type type) {
		throw new UnsupportedOperationException("Not supported: " + type.class)
	}

	public def dispatch Type toType(TypeReference type) {
		type.reference.type.toType
	}

	public def dispatch Type toType(BooleanTypeDefinition type) {
		Bool
	}

	public def dispatch Type toType(IntegerTypeDefinition type) {
		Int
	}

	public def dispatch Type toType(RealTypeDefinition type) {
		Rat
	}

	public def dispatch Type toType(FunctionTypeDefinition type) {
		val parameterTypes = type.parameterTypes
		if (parameterTypes.size == 0) {
			throw new UnsupportedOperationException("TODO")
		}
		if (parameterTypes.size == 1) {
			val paramType = parameterTypes.get(0).toType
			val resultType = type.returnType.toType
			Func(paramType, resultType)
		} else {
			throw new UnsupportedOperationException("TODO")
		}
	}

	public def dispatch Type toType(ArrayTypeDefinition type) {
		val indexTypes = type.indexTypes
		if (indexTypes.size == 0) {
			throw new UnsupportedOperationException("TODO")
		}
		if (indexTypes.size == 1) {
			val indexType = indexTypes.get(0).toType
			val elemType = type.elementType.toType
			Array(indexType, elemType)
		} else {
			throw new UnsupportedOperationException("TODO")
		}
	}
	
}
