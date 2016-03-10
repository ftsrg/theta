package hu.bme.mit.inf.ttmc.system.ui

import hu.bme.mit.inf.ttmc.constraint.decl.Decl
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.ui.TypeHelper
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.formalism.common.factory.STSFactory
import hu.bme.mit.inf.ttmc.system.model.VariableDeclaration
import java.util.HashMap
import java.util.Map

class SystemDeclarationHelper extends DeclarationHelper {

	protected val extension STSFactory stsFactory

	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar

	protected new(DeclFactory declFactory, STSFactory stsFactory, TypeHelper typeHelper) {
		super(declFactory, typeHelper)
		this.stsFactory = stsFactory
		variableToVar = new HashMap
	}
	
	////
	
	
	public def dispatch Decl<Type> toDecl(VariableDeclaration declaration) {
		var varDecl = variableToVar.get(declaration)
		if (varDecl === null) {
			val name = declaration.name
			val type = declaration.type.toType
			varDecl = Var(name, type)
			variableToVar.put(declaration, varDecl)
		}
		varDecl
	}
	
}