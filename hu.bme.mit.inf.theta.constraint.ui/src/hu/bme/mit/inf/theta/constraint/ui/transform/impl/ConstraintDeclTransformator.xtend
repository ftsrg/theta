package hu.bme.mit.inf.theta.constraint.ui.transform.impl

import hu.bme.mit.inf.theta.constraint.model.ConstantDeclaration
import hu.bme.mit.inf.theta.constraint.model.Declaration
import hu.bme.mit.inf.theta.constraint.model.FunctionDeclaration
import hu.bme.mit.inf.theta.constraint.model.ParameterDeclaration
import hu.bme.mit.inf.theta.constraint.ui.transform.DeclTransformator
import hu.bme.mit.inf.theta.constraint.ui.transform.TransformationManager
import hu.bme.mit.inf.theta.constraint.ui.transform.TypeTransformator
import hu.bme.mit.inf.theta.core.decl.ConstDecl
import hu.bme.mit.inf.theta.core.decl.Decl
import hu.bme.mit.inf.theta.core.decl.ParamDecl
import hu.bme.mit.inf.theta.core.type.Type
import java.util.HashMap
import java.util.List
import java.util.Map

import static hu.bme.mit.inf.theta.core.decl.impl.Decls.*
import static hu.bme.mit.inf.theta.core.type.impl.Types.*

public class ConstraintDeclTransformator implements DeclTransformator {
	
	private val Map<Declaration, ConstDecl<Type>> constantToConst
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
		var constDecl = constantToConst.get(declaration)
		if (constDecl === null) {
			val name = declaration.name
			val paramDecls = declaration.parameterDeclarations.map[it._toDecl].toList
			val returnType = declaration.type.transform
			val type = toFuncType(paramDecls.map[type], returnType)
			constDecl = Const(name, type)
			constantToConst.put(declaration, constDecl)
		}
		constDecl
	}
	
	private def Type toFuncType(List<Type> paramTypes, Type returnType) {
		if (paramTypes.empty) {
			returnType
		} else {
			val pref = paramTypes.subList(0, paramTypes.size - 1)
			val last = paramTypes.last
			toFuncType(pref, Func(last, returnType))
		}
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