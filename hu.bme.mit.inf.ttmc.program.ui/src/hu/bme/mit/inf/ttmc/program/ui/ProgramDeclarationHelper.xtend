package hu.bme.mit.inf.ttmc.program.ui

import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.ui.TypeHelper
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.program.model.VariableDeclaration
import java.util.HashMap
import java.util.Map
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramDeclFactory

class ProgramDeclarationHelper extends DeclarationHelper {
	
	private val extension ProgramDeclFactory declFactory
	
	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar
	
	new(ProgramDeclFactory declFactory, TypeHelper typeHelper) {
		super(declFactory, typeHelper)
		this.declFactory = declFactory
		variableToVar = new HashMap
	}
	
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