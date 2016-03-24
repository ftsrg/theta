package hu.bme.mit.inf.ttmc.program.ui.transform.impl

import hu.bme.mit.inf.ttmc.constraint.model.Expression
import hu.bme.mit.inf.ttmc.constraint.model.ReferenceExpression
import hu.bme.mit.inf.ttmc.constraint.type.BoolType
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator
import hu.bme.mit.inf.ttmc.constraint.ui.transform.ExprTransformator
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
import hu.bme.mit.inf.ttmc.program.model.Statement
import hu.bme.mit.inf.ttmc.program.model.WhileStatement
import hu.bme.mit.inf.ttmc.program.ui.transform.StmtTransformator
import java.util.LinkedList

import static com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.inf.ttmc.constraint.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.model.Declaration
import hu.bme.mit.inf.ttmc.constraint.decl.Decl

class ProgramStmtTransformator implements StmtTransformator {

	private val ProgramTransformationManager manager
	private val extension StmtFactory stmtFactory;
	
	private volatile DeclTransformator dt;
	private volatile ExprTransformator et;

	new(ProgramTransformationManager manager, StmtFactory stmtFactory) {
		this.manager = manager
		this.stmtFactory = stmtFactory

	}
	
	////////
	
	private def DeclTransformator getDeclTransformator() {
		if (dt === null) {
			dt = manager.declTransformator
		}
		dt
	}
	
	private def ExprTransformator getExprTransformator() {
		if (et === null) {
			et = manager.exprTransformator
		}
		et
	}
	
	private def Decl<? extends Type, ?> transform(Declaration declaration) {
		declTransformator.transform(declaration)
	}
	
	private def Expr<? extends Type> transform(Expression expression) {
		exprTransformator.transform(expression)
	}
	
	////////
	
	override transform(Statement statement) {
		statement.toStmt
	}
	
	///////

	protected def dispatch Stmt toStmt(AssumeStatement statement) {
		val cond = ExprUtils.cast(statement.expression.transform, BoolType)
		Assume(cond)
	}

	protected def dispatch Stmt toStmt(AssertStatement statement) {
		val cond = ExprUtils.cast(statement.expression.transform, BoolType)
		Assert(cond)
	}

	protected def dispatch Stmt toStmt(AssignmentStatement statement) {
		val varDecl = statement.lhsExpression.extractVar
		val expr = statement.rhsExpression.transform
		Assign(varDecl, expr)
	}

	protected def dispatch Stmt toStmt(HavocStatement statement) {
		val varDecl = statement.expression.extractVar
		Havoc(varDecl)
	}

	protected def dispatch Stmt toStmt(SkipStatement statement) {
		Skip
	}

	protected def dispatch Stmt toStmt(BlockStatement statement) {
		val stmts = new LinkedList
		for (variableDeclaration : statement.variableDeclarations) {
			if (variableDeclaration.expression !== null) {
				val varDecl = variableDeclaration.transform as VarDecl<Type>
				val value = variableDeclaration.expression.transform
				val assign = Assign(varDecl, value)
				stmts.add(assign)
			}
		}
		val blockStmts = statement.statements.map[toStmt]
		stmts.addAll(blockStmts)
		Block(stmts)
	}

	protected def dispatch Stmt toStmt(ReturnStatement statement) {
		val expr = statement.expression.transform
		Return(expr)
	}

	protected def dispatch Stmt toStmt(IfStatement statement) {
		checkArgument(statement.conditionExpression != null, "Nondeterministic statements are not supported")

		val cond = ExprUtils.cast(statement.conditionExpression.transform, BoolType)
		val then = statement.thenStatement.toStmt
		if (statement.elseStatement == null) {
			If(cond, then)
		} else {
			val elze = statement.elseStatement.toStmt
			If(cond, then, elze)
		}
	}

	protected def dispatch Stmt toStmt(WhileStatement statement) {
		checkArgument(statement.conditionExpression != null, "Nondeterministic statements are not supported")

		val cond = ExprUtils.cast(statement.conditionExpression.transform, BoolType)
		val doStmt = statement.doStatement.toStmt
		While(cond, doStmt)
	}

	protected def dispatch Stmt toStmt(DoStatement statement) {
		checkArgument(statement.conditionExpression != null, "Nondeterministic statements are not supported")

		val doStmt = statement.doStatement.toStmt
		val cond = ExprUtils.cast(statement.conditionExpression.transform, BoolType)
		Do(doStmt, cond)
	}

	// //////
	private def VarDecl<Type> extractVar(Expression expression) {
		if (expression instanceof ReferenceExpression) {
			val decl = expression.declaration.transform
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
