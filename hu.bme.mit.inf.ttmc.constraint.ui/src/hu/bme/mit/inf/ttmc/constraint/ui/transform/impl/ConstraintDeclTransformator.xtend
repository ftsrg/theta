package hu.bme.mit.inf.ttmc.constraint.ui.transform.impl

import java.util.Map
import hu.bme.mit.inf.ttmc.constraint.model.ConstantDeclaration
import hu.bme.mit.inf.ttmc.core.decl.ConstDecl
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl
import hu.bme.mit.inf.ttmc.constraint.model.ParameterDeclaration
import hu.bme.mit.inf.ttmc.core.decl.Decl
import hu.bme.mit.inf.ttmc.constraint.model.Declaration
import java.util.HashMap
import hu.bme.mit.inf.ttmc.core.type.Type
import hu.bme.mit.inf.ttmc.constraint.model.FunctionDeclaration
import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TypeTransformator

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.*;

public class ConstraintDeclTransformator implements DeclTransformator {
	
	private val Map<ConstantDeclaration, ConstDecl<Type>> constantToConst
	private val Map<ParameterDeclaration, ParamDecl<Type>> parameterToParam
		
	private val extension TypeTransformator tt
	
	public new(TransformationManager manager) {
		tt = manager.typeTransformator
		constantToConst = new HashMap()
		parameterToParam = new HashMap()
	}
	
	////////
	
	override transform(Declaration declaration) {
		return declaration.toDecl
	}
	
	////////
	
	protected def dispatch Decl<? extends Type, ?> toDecl(Declaration declaration) {
		throw new UnsupportedOperationException("Not supported: " + declaration.class)
	}

	protected def dispatch ConstDecl<Type> toDecl(ConstantDeclaration declaration) {
		var constDecl = constantToConst.get(declaration)
		if (constDecl === null) {
			val name = declaration.name
			val type = declaration.type.transform
			constDecl = Const(name, type)
			constantToConst.put(declaration, constDecl)
		}
		constDecl
	}

	protected def dispatch ConstDecl<Type> toDecl(FunctionDeclaration declaration) {
		throw new UnsupportedOperationException("TODO")
	}

	protected def dispatch ParamDecl<Type> toDecl(ParameterDeclaration declaration) {
		var paramDecl = parameterToParam.get(declaration)
		if (paramDecl === null) {
			val name = declaration.name
			val type = declaration.type.transform
			paramDecl = Param(name, type)
			parameterToParam.put(declaration, paramDecl)
		}
		return paramDecl
	}

}