package hu.bme.mit.inf.ttmc.program.ui.transform.impl

import hu.bme.mit.inf.ttmc.core.type.Type
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.program.model.VariableDeclaration
import java.util.HashMap
import java.util.Map
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramDeclFactory
import hu.bme.mit.inf.ttmc.program.model.ProcedureDeclaration
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl
import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintDeclTransformator
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TypeTransformator
import hu.bme.mit.inf.ttmc.program.model.Statement
import hu.bme.mit.inf.ttmc.program.ui.transform.StmtTransformator
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt

class ProgramDeclTransformator extends ConstraintDeclTransformator {

	private val ProgramTransformationManager manager
	private val extension ProgramDeclFactory declFactory
	
	
	private volatile TypeTransformator tt
	private volatile StmtTransformator st
	
	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar
	private val Map<ProcedureDeclaration, ProcDecl<Type>> procedureToProc
	
	new(ProgramTransformationManager manager, ProgramDeclFactory declFactory) {
		super(manager, declFactory)
		this.manager = manager
		this.declFactory = declFactory
		variableToVar = new HashMap
		procedureToProc = new HashMap
	}
	
	
	////////
	
	private def TypeTransformator getTypeTransformator() {
		if (tt === null) {
			tt = manager.typeTransformator
		}
		tt
	}
	
	private def StmtTransformator getStmtTransformator() {
		if (st === null) {
			st = manager.stmtTransformator
		}
		st
	}
	
	private def Type transform(hu.bme.mit.inf.ttmc.constraint.model.Type type) {
		typeTransformator.transform(type)
	}
	
	private def Stmt transform(Statement statement) {
		stmtTransformator.transform(statement)
	}
	
	////////
	
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
			val Statement statement = declaration.statement
			
			if (statement === null) {
				procDecl = Proc(name, paramDecls, returnType)
			} else {
				val Stmt stmt = statement.transform
				procDecl = Proc(name, paramDecls, returnType, stmt)
			}
			procedureToProc.put(declaration, procDecl)
		}
		procDecl
	}
	
}