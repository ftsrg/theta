package hu.bme.mit.inf.theta.program.ui.transform.impl

import hu.bme.mit.inf.theta.core.type.Type
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl
import hu.bme.mit.inf.theta.program.model.VariableDeclaration
import java.util.HashMap
import java.util.Map
import hu.bme.mit.inf.theta.program.model.ProcedureDeclaration
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl
import hu.bme.mit.inf.theta.constraint.ui.transform.impl.ConstraintDeclTransformator
import hu.bme.mit.inf.theta.constraint.ui.transform.TypeTransformator

import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.*;

class ProgramDeclTransformator extends ConstraintDeclTransformator {

	private val ProgramTransformationManager manager
	
	private volatile TypeTransformator tt
//	private volatile StmtTransformator st
	
	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar
	private val Map<ProcedureDeclaration, ProcDecl<Type>> procedureToProc
	
	new(ProgramTransformationManager manager) {
		super(manager)
		this.manager = manager
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
	
//	private def StmtTransformator getStmtTransformator() {
//		if (st === null) {
//			st = manager.stmtTransformator
//		}
//		st
//	}
	
	private def Type transform(hu.bme.mit.inf.theta.constraint.model.Type type) {
		typeTransformator.transform(type)
	}
	
//	private def Stmt transform(Statement statement) {
//		stmtTransformator.transform(statement)
//	}
	
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
//			val Statement statement = declaration.statement
			procDecl = Proc(name, paramDecls, returnType)
			procedureToProc.put(declaration, procDecl)
		}
		procDecl
	}
	
}