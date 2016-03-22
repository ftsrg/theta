package hu.bme.mit.inf.ttmc.system.ui

import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.ui.TypeHelper
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory
import hu.bme.mit.inf.ttmc.system.model.VariableDeclaration
import java.util.HashMap
import java.util.Map

class SystemDeclarationHelper extends DeclarationHelper {

	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar

	private val extension VarDeclFactory varDeclFactory;

	protected new(VarDeclFactory declFactory, TypeHelper typeHelper) {
		super(declFactory, typeHelper)
		varDeclFactory = declFactory
		variableToVar = new HashMap
	}
	
	////
	
	
	public def dispatch VarDecl<Type> toDecl(VariableDeclaration declaration) {
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