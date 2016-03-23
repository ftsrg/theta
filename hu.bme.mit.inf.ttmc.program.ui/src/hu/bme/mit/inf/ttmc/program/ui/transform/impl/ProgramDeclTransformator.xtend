package hu.bme.mit.inf.ttmc.program.ui.transform.impl

import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.program.model.VariableDeclaration
import java.util.HashMap
import java.util.Map
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramDeclFactory
import hu.bme.mit.inf.ttmc.program.model.ProcedureDeclaration
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl
import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintDeclTransformator
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TypeTransformator

class ProgramDeclTransformator extends ConstraintDeclTransformator {
	
	private val extension ProgramDeclFactory declFactory
	
	private val extension TypeTransformator tt
	
	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar
	private val Map<ProcedureDeclaration, ProcDecl<Type>> procedureToProc
	
	new(ProgramTransformationManager manager, ProgramDeclFactory declFactory) {
		super(manager, declFactory)
		this.declFactory = declFactory
		tt = manager.typeTransformator
		variableToVar = new HashMap
		procedureToProc = new HashMap
	}
	
	////
	
	public def dispatch VarDecl<Type> toDecl(VariableDeclaration declaration) {
		var varDecl = variableToVar.get(declaration)
		if (varDecl === null) {
			val name = declaration.name
			val type = declaration.type.transform
			varDecl = Var(name, type)
			variableToVar.put(declaration, varDecl)
		}
		varDecl
	}
	
	public def dispatch ProcDecl<Type> toDecl(ProcedureDeclaration declaration) {
		var procDecl = procedureToProc.get(declaration)
		if (procDecl === null) {
			val name = declaration.name
			val returnType = declaration.type.transform
			val paramDecls = declaration.parameterDeclarations.map[_toDecl]
			procDecl = Proc(name, paramDecls, returnType)
			procedureToProc.put(declaration, procDecl)
		}
		procDecl
	}
	
}