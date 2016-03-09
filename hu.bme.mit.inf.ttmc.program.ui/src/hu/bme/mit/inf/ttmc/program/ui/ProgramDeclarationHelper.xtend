package hu.bme.mit.inf.ttmc.program.ui

import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory
import hu.bme.mit.inf.ttmc.constraint.ui.TypeHelper
import java.util.HashMap
import java.util.Map
import hu.bme.mit.inf.ttmc.program.model.VariableDeclaration
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl
import hu.bme.mit.inf.ttmc.formalism.factory.ProgramFactory
import hu.bme.mit.inf.ttmc.constraint.type.Type

class ProgramDeclarationHelper extends DeclarationHelper {
	
	private val extension ProgramFactory programFactory
	
	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar
	
	new(DeclFactory declFactory, ProgramFactory factory, TypeHelper typeHelper) {
		super(declFactory, typeHelper)
		this.programFactory = programFactory
		variableToVar = new HashMap
	}
	
	public def dispatch VarDecl<hu.bme.mit.inf.ttmc.constraint.type.Type> toDecl(VariableDeclaration declaration) {
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