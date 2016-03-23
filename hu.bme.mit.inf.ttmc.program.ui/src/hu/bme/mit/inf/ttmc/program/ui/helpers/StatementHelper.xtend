package hu.bme.mit.inf.ttmc.program.ui.helpers

import hu.bme.mit.inf.ttmc.constraint.model.Expression
import hu.bme.mit.inf.ttmc.constraint.model.ReferenceExpression
import hu.bme.mit.inf.ttmc.constraint.type.BoolType
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl
import hu.bme.mit.inf.ttmc.formalism.common.factory.StmtFactory
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt
import hu.bme.mit.inf.ttmc.program.model.AssertStatement
import hu.bme.mit.inf.ttmc.program.model.AssignmentStatement
import hu.bme.mit.inf.ttmc.program.model.AssumeStatement
import hu.bme.mit.inf.ttmc.program.model.BlockStatement
import hu.bme.mit.inf.ttmc.program.model.DoStatement
import hu.bme.mit.inf.ttmc.program.model.HavocStatement
import hu.bme.mit.inf.ttmc.program.model.IfStatement
import hu.bme.mit.inf.ttmc.program.model.ReturnStatement
import hu.bme.mit.inf.ttmc.program.model.SkipStatement
import hu.bme.mit.inf.ttmc.program.model.WhileStatement
import java.util.LinkedList

import static com.google.common.base.Preconditions.checkArgument

class StatementHelper {

	private val extension StmtFactory stmtFactory;

	private val extension ProgramDeclarationHelper declarationHelper
	private val extension ProgramExpressionHelper expressionHelper

	new(StmtFactory stmtFactory, ProgramDeclarationHelper declarationHelper, ProgramExpressionHelper expressionHelper) {
		this.stmtFactory = stmtFactory
		this.declarationHelper = declarationHelper
		this.expressionHelper = expressionHelper
	}

	public def dispatch Stmt toStmt(AssumeStatement statement) {
		val cond = ExprUtils.cast(statement.expression.toExpr, BoolType)
		Assume(cond)
	}

	public def dispatch Stmt toStmt(AssertStatement statement) {
		val cond = ExprUtils.cast(statement.expression.toExpr, BoolType)
		Assert(cond)
	}

	public def dispatch Stmt toStmt(AssignmentStatement statement) {
		val varDecl = statement.lhsExpression.extractVar
		val expr = statement.rhsExpression.toExpr
		Assign(varDecl, expr)
	}

	public def dispatch Stmt toStmt(HavocStatement statement) {
		val varDecl = statement.expression.extractVar
		Havoc(varDecl)
	}

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
		checkArgument(statement.conditionExpression != null, "Nondeterministic statements are not supported")

		val cond = ExprUtils.cast(statement.conditionExpression.toExpr, BoolType)
		val then = statement.thenStatement.toStmt
		if (statement.elseStatement == null) {
			If(cond, then)
		} else {
			val elze = statement.elseStatement.toStmt
			If(cond, then, elze)
		}
	}

	public def dispatch Stmt toStmt(WhileStatement statement) {
		checkArgument(statement.conditionExpression != null, "Nondeterministic statements are not supported")

		val cond = ExprUtils.cast(statement.conditionExpression.toExpr, BoolType)
		val doStmt = statement.doStatement.toStmt
		While(cond, doStmt)
	}

	public def dispatch Stmt toStmt(DoStatement statement) {
		checkArgument(statement.conditionExpression != null, "Nondeterministic statements are not supported")

		val doStmt = statement.doStatement.toStmt
		val cond = ExprUtils.cast(statement.conditionExpression.toExpr, BoolType)
		Do(doStmt, cond)
	}

	// //////
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

}
