package hu.bme.mit.inf.ttmc.program.ui

import hu.bme.mit.inf.ttmc.constraint.model.Expression
import hu.bme.mit.inf.ttmc.constraint.model.ReferenceExpression
import hu.bme.mit.inf.ttmc.program.model.AssertStatement
import hu.bme.mit.inf.ttmc.program.model.AssignmentStatement
import hu.bme.mit.inf.ttmc.program.model.AssumeStatement
import hu.bme.mit.inf.ttmc.program.model.BlockStatement
import hu.bme.mit.inf.ttmc.program.model.DoStatement
import hu.bme.mit.inf.ttmc.program.model.HavocStatement
import hu.bme.mit.inf.ttmc.program.model.IfStatement
import hu.bme.mit.inf.ttmc.program.model.ReturnStatement
import hu.bme.mit.inf.ttmc.program.model.SkipStatement
import hu.bme.mit.inf.ttmc.program.model.VariableDeclaration
import hu.bme.mit.inf.ttmc.program.model.WhileStatement
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager
import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr
import hu.bme.mit.inf.ttmc.constraint.type.BoolType
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.program.decl.VarDecl
import hu.bme.mit.inf.ttmc.program.factory.ProgramFactory
import hu.bme.mit.inf.ttmc.program.stmt.Stmt
import java.util.HashMap
import java.util.Map
import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModelHelper
import java.util.LinkedList

public class ProgramModelHelper extends ConstraintModelHelper {
	
	private val extension ProgramFactory pf
	
	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar
	
	public new(ConstraintManager manager, ProgramFactory factory) {
		super(manager)
		pf = factory
		variableToVar = new HashMap
	}
	
	///////
	
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
	
	////////
	
	protected def dispatch RefExpr<? extends Type, ?> toRefExpr(VariableDeclaration declaration) {
		val decl = declaration.toDecl
		val varDecl = decl as VarDecl<Type>
		Ref(varDecl)

	}
	
	////////
	
	public def dispatch Stmt toStmt(AssumeStatement statement) {
		val cond = statement.expression.toExpr.withType(BoolType)
		Assume(cond)
	}
	
	public def dispatch Stmt toStmt(AssertStatement statement) {
		val cond = statement.expression.toExpr.withType(BoolType)
		Assert(cond)
	}
	
	public def dispatch Stmt toStmt(AssignmentStatement statement) {
		val varDecl = statement.lhsExpression.extractVar
		val expr = statement.rhsExpression.toExpr
		Assign(varDecl, expr)
	}
	
	////
	
	public def dispatch Stmt toStmt(HavocStatement statement) {
		val varDecl = statement.expression.extractVar
		Havoc(varDecl)
	}
	
	private def VarDecl<Type> extractVar(Expression expression) {
		if (expression instanceof ReferenceExpression) {
			val decl = expression.declaration.toDecl
			if (decl instanceof VarDecl<?>) {
				val varDecl = decl as VarDecl<Type>
				varDecl
			} else {
				throw new UnsupportedOperationException("Only assignments to variables are allowed.")
			}
		} else {
			throw new UnsupportedOperationException("Only assignments to simple identifiers is supported.")
		}
	}
	
	////
	
	public def dispatch Stmt toStmt(SkipStatement statement) {
		Skip
	}
	
	public def dispatch Stmt toStmt(BlockStatement statement) {
		val stmts = new LinkedList
		for (variableDeclaration : statement.variableDeclarations) {
			if (variableDeclaration.expression !== null) {
				val varDecl = variableDeclaration.toDecl as VarDecl<Type>
				val value = variableDeclaration.expression.toExpr
				val assign = Assign(varDecl, value)
				stmts.add(assign)
			}
		}
		val blockStmts = statement.statements.map[toStmt]
		stmts.addAll(blockStmts)
		Block(stmts)
	}
	
	public def dispatch Stmt toStmt(ReturnStatement statement) {
		val expr = statement.expression.toExpr
		Return(expr)
	}
	
	public def dispatch Stmt toStmt(IfStatement statement) {
		if (statement.conditionExpression != null) {
			val cond = statement.conditionExpression.toExpr.withType(BoolType)
			val then = statement.thenStatement.toStmt
			if (statement.elseStatement == null) {
				If(cond, then)
			} else {
				val elze = statement.elseStatement.toStmt
				If(cond, then, elze)
			}
		} else {
			throw new UnsupportedOperationException("Nondeterministic if-statements are not supported")
		}
	}
	
	public def dispatch Stmt toStmt(WhileStatement statement) {
		if (statement.conditionExpression != null) {
			val cond = statement.conditionExpression.toExpr.withType(BoolType)
			val doStmt = statement.doStatement.toStmt
			While(cond, doStmt)
		} else {
			throw new UnsupportedOperationException("Nondeterministic while-statements are not supported")
		}
	}
	
	public def dispatch Stmt toStmt(DoStatement statement) {
		if (statement.conditionExpression != null) {
			val doStmt = statement.doStatement.toStmt
			val cond = statement.conditionExpression.toExpr.withType(BoolType)
			Do(doStmt, cond)
		} else {
			throw new UnsupportedOperationException("Nondeterministic do-statements are not supported")
		}
	}
}