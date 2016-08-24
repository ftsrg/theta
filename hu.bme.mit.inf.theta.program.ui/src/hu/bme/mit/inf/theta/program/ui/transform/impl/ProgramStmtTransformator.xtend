package hu.bme.mit.inf.theta.program.ui.transform.impl

import hu.bme.mit.inf.theta.constraint.model.Declaration
import hu.bme.mit.inf.theta.constraint.model.Expression
import hu.bme.mit.inf.theta.constraint.model.ReferenceExpression
import hu.bme.mit.inf.theta.constraint.ui.transform.DeclTransformator
import hu.bme.mit.inf.theta.constraint.ui.transform.ExprTransformator
import hu.bme.mit.inf.theta.core.decl.Decl
import hu.bme.mit.inf.theta.core.expr.Expr
import hu.bme.mit.inf.theta.core.type.BoolType
import hu.bme.mit.inf.theta.core.type.Type
import hu.bme.mit.inf.theta.core.utils.impl.ExprUtils
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt
import hu.bme.mit.inf.theta.program.model.AssertStatement
import hu.bme.mit.inf.theta.program.model.AssignmentStatement
import hu.bme.mit.inf.theta.program.model.AssumeStatement
import hu.bme.mit.inf.theta.program.model.BlockStatement
import hu.bme.mit.inf.theta.program.model.DeclarationStatement
import hu.bme.mit.inf.theta.program.model.DoStatement
import hu.bme.mit.inf.theta.program.model.HavocStatement
import hu.bme.mit.inf.theta.program.model.IfStatement
import hu.bme.mit.inf.theta.program.model.ReturnStatement
import hu.bme.mit.inf.theta.program.model.SkipStatement
import hu.bme.mit.inf.theta.program.model.Statement
import hu.bme.mit.inf.theta.program.model.WhileStatement
import hu.bme.mit.inf.theta.program.ui.transform.StmtTransformator

import static com.google.common.base.Preconditions.checkArgument

import static hu.bme.mit.inf.theta.formalism.common.stmt.impl.Stmts.*;
import hu.bme.mit.inf.theta.formalism.utils.StmtUtils

class ProgramStmtTransformator implements StmtTransformator {

	private val ProgramTransformationManager manager
	
	private volatile DeclTransformator dt;
	private volatile ExprTransformator et;

	new(ProgramTransformationManager manager) {
		this.manager = manager
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
	
	protected def dispatch Stmt toStmt(DeclarationStatement statement) {
		val variableDeclaration = statement.variableDeclaration
		val VarDecl<? extends Type> varDecl = variableDeclaration.transform as VarDecl<? extends Type>
		
		val expression = variableDeclaration.expression
		if (expression === null) {
			Decl(varDecl)
		} else {
			val expr = ExprUtils.cast(expression.transform, varDecl.type.class)
			Decl(varDecl as VarDecl<Type>, expr)
		}
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
		val subStmts = statement.statements.map[toStmt]
		
		if (subStmts.size == 1) {
			subStmts.get(0)
		} else {
			Block(subStmts.map[StmtUtils::getSubStmts(it)].flatten.toList)
		}
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

	////////
	
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
