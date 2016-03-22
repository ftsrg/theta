package hu.bme.mit.inf.ttmc.constraint.ui

import java.util.Map
import hu.bme.mit.inf.ttmc.constraint.model.ConstantDeclaration
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl
import hu.bme.mit.inf.ttmc.constraint.model.ParameterDeclaration
import hu.bme.mit.inf.ttmc.constraint.decl.Decl
import hu.bme.mit.inf.ttmc.constraint.model.Declaration
import java.util.HashMap
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.model.FunctionDeclaration

class DeclarationHelper {
	
	protected val Map<ConstantDeclaration, ConstDecl<Type>> constantToConst
	protected val Map<ParameterDeclaration, ParamDecl<Type>> parameterToParam
	
	protected val extension DeclFactory declFactory
	protected val extension TypeHelper typeHelper
	
	public new(DeclFactory declFactory, TypeHelper typeHelper) {
		this.declFactory = declFactory
		this.typeHelper = typeHelper
		constantToConst = new HashMap()
		parameterToParam = new HashMap()
	}
	
	////////
	
	public def dispatch Decl<Type, ?> toDecl(Declaration declaration) {
		throw new UnsupportedOperationException("Not supported: " + declaration.class)
	}

	public def dispatch ConstDecl<Type> toDecl(ConstantDeclaration declaration) {
		var constDecl = constantToConst.get(declaration)
		if (constDecl === null) {
			val name = declaration.name
			val type = declaration.type.toType
			constDecl = Const(name, type)
			constantToConst.put(declaration, constDecl)
		}
		constDecl
	}

	public def dispatch ConstDecl<Type> toDecl(FunctionDeclaration declaration) {
		throw new UnsupportedOperationException("TODO")
	}

	public def dispatch ParamDecl<Type> toDecl(ParameterDeclaration declaration) {
		var paramDecl = parameterToParam.get(declaration)
		if (paramDecl === null) {
			val name = declaration.name
			val type = declaration.type.toType
			paramDecl = Param(name, type)
			parameterToParam.put(declaration, paramDecl)
		}
		return paramDecl
	}
	
}