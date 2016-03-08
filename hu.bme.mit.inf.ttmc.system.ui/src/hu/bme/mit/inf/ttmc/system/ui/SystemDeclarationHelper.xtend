package hu.bme.mit.inf.ttmc.system.ui

import hu.bme.mit.inf.ttmc.constraint.ui.DeclarationHelper
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory
import hu.bme.mit.inf.ttmc.constraint.ui.TypeHelper
import hu.bme.mit.inf.ttmc.formalism.factory.ProgramFactory
import hu.bme.mit.inf.ttmc.constraint.decl.Decl
import hu.bme.mit.inf.ttmc.system.model.VariableDeclaration
import hu.bme.mit.inf.ttmc.constraint.type.Type
import java.util.HashMap
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl
import java.util.Map

class SystemDeclarationHelper extends DeclarationHelper {

	protected val extension ProgramFactory programFactory

	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar

	protected new(DeclFactory declFactory, ProgramFactory programFactory, TypeHelper typeHelper) {
		super(declFactory, typeHelper)
		this.programFactory = programFactory
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