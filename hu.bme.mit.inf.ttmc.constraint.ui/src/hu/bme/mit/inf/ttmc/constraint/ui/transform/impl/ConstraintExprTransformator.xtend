package hu.bme.mit.inf.ttmc.constraint.ui.transform.impl

import hu.bme.mit.inf.ttmc.constraint.model.AddExpression
import hu.bme.mit.inf.ttmc.constraint.model.AndExpression
import hu.bme.mit.inf.ttmc.constraint.model.ArrayAccessExpression
import hu.bme.mit.inf.ttmc.constraint.model.ArrayWithExpression
import hu.bme.mit.inf.ttmc.constraint.model.DecimalLiteralExpression
import hu.bme.mit.inf.ttmc.constraint.model.DivExpression
import hu.bme.mit.inf.ttmc.constraint.model.DivideExpression
import hu.bme.mit.inf.ttmc.constraint.model.EqualExpression
import hu.bme.mit.inf.ttmc.constraint.model.EqualityExpression
import hu.bme.mit.inf.ttmc.constraint.model.Expression
import hu.bme.mit.inf.ttmc.constraint.model.FalseExpression
import hu.bme.mit.inf.ttmc.constraint.model.GreaterEqualExpression
import hu.bme.mit.inf.ttmc.constraint.model.GreaterExpression
import hu.bme.mit.inf.ttmc.constraint.model.IfThenElseExpression
import hu.bme.mit.inf.ttmc.constraint.model.ImplyExpression
import hu.bme.mit.inf.ttmc.constraint.model.InequalityExpression
import hu.bme.mit.inf.ttmc.constraint.model.IntegerLiteralExpression
import hu.bme.mit.inf.ttmc.constraint.model.LessEqualExpression
import hu.bme.mit.inf.ttmc.constraint.model.LessExpression
import hu.bme.mit.inf.ttmc.constraint.model.ModExpression
import hu.bme.mit.inf.ttmc.constraint.model.MultiplyExpression
import hu.bme.mit.inf.ttmc.constraint.model.NotExpression
import hu.bme.mit.inf.ttmc.constraint.model.OrExpression
import hu.bme.mit.inf.ttmc.constraint.model.RationalLiteralExpression
import hu.bme.mit.inf.ttmc.constraint.model.ReferenceExpression
import hu.bme.mit.inf.ttmc.constraint.model.SubtractExpression
import hu.bme.mit.inf.ttmc.constraint.model.TrueExpression
import hu.bme.mit.inf.ttmc.constraint.model.UnaryMinusExpression
import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator
import hu.bme.mit.inf.ttmc.constraint.ui.transform.ExprTransformator
import hu.bme.mit.inf.ttmc.constraint.ui.transform.TransformationManager
import hu.bme.mit.inf.ttmc.core.expr.Expr
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory
import hu.bme.mit.inf.ttmc.core.type.ArrayType
import hu.bme.mit.inf.ttmc.core.type.BoolType
import hu.bme.mit.inf.ttmc.core.type.IntType
import hu.bme.mit.inf.ttmc.core.type.RatType
import hu.bme.mit.inf.ttmc.core.type.Type
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils

public class ConstraintExprTransformator implements ExprTransformator {

	private val extension ExprFactory exprFactory
	
	private val extension DeclTransformator df
	
	public new(TransformationManager manager, ExprFactory exprFactory) {
		this.exprFactory = exprFactory
		df = manager.declTransformator
	}
		
	////
		
	override transform(Expression expression) {
		return expression.toExpr
	}
	
	////
	
	protected def dispatch Expr<? extends Type> toExpr(Expression expression) {
		throw new UnsupportedOperationException("Not supported: " + expression.class)
	}

	protected def dispatch Expr<? extends Type> toExpr(TrueExpression expression) {
		True
	}

	protected def dispatch Expr<? extends Type> toExpr(FalseExpression expression) {
		False
	}

	protected def dispatch Expr<? extends Type> toExpr(IntegerLiteralExpression expression) {
		val value = expression.value.longValueExact
		Int(value)
	}

	protected def dispatch Expr<? extends Type> toExpr(RationalLiteralExpression expression) {
		val num = expression.numerator.longValueExact
		val denom = expression.denominator.longValueExact
		Rat(num, denom)
	}

	protected def dispatch Expr<? extends Type> toExpr(DecimalLiteralExpression expression) {
		throw new UnsupportedOperationException("ToDo")
	}

	protected def dispatch Expr<? extends Type> toExpr(AddExpression expression) {
		val ops = expression.operands.map[ExprUtils.cast(toExpr, ClosedUnderAdd)]
		Add(ops)
	}

	protected def dispatch Expr<? extends Type> toExpr(MultiplyExpression expression) {
		val ops = expression.operands.map[ExprUtils.cast(toExpr, ClosedUnderMul)]
		Mul(ops)
	}

	protected def dispatch Expr<? extends Type> toExpr(UnaryMinusExpression expression) {
		val op = ExprUtils.cast(expression.operand.toExpr, ClosedUnderNeg)
		Neg(op)
	}

	protected def dispatch Expr<? extends Type> toExpr(SubtractExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, ClosedUnderSub)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, ClosedUnderSub)
		Sub(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(DivideExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, RatType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, RatType)
		RatDiv(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(DivExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, IntType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, IntType)
		IntDiv(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(ModExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, IntType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, IntType)
		IntDiv(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(EqualityExpression expression) {
		val leftOp = expression.leftOperand.toExpr
		val rightOp = expression.rightOperand.toExpr
		Eq(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(InequalityExpression expression) {
		val leftOp = expression.leftOperand.toExpr
		val rightOp = expression.rightOperand.toExpr
		Neq(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(LessExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, RatType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, RatType)
		Lt(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(LessEqualExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, RatType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, RatType)
		Leq(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(GreaterExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, RatType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, RatType)
		Gt(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(GreaterEqualExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, RatType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, RatType)
		Geq(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(NotExpression expression) {
		val op = ExprUtils.cast(expression.operand.toExpr, BoolType)
		Not(op)
	}

	protected def dispatch Expr<? extends Type> toExpr(ImplyExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, BoolType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, BoolType)
		Imply(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(EqualExpression expression) {
		val leftOp = ExprUtils.cast(expression.leftOperand.toExpr, BoolType)
		val rightOp = ExprUtils.cast(expression.rightOperand.toExpr, BoolType)
		Iff(leftOp, rightOp)
	}

	protected def dispatch Expr<? extends Type> toExpr(AndExpression expression) {
		val ops = expression.operands.map[ExprUtils.cast(toExpr, BoolType)]
		And(ops)
	}

	protected def dispatch Expr<? extends Type> toExpr(OrExpression expression) {
		val ops = expression.operands.map[ExprUtils.cast(toExpr, BoolType)]
		Or(ops)
	}

	protected def dispatch Expr<? extends Type> toExpr(ArrayAccessExpression expression) {
		val array = ExprUtils.cast(expression.operand.toExpr, ArrayType) as Expr<ArrayType<Type, Type>>

		val parameters = expression.parameters
		if (parameters.size == 0) {
			throw new UnsupportedOperationException
		} else if (parameters.size == 1) {
			val parameter = expression.parameters.get(0)
			val index = parameter.toExpr
			Read(array, index)
		} else {
			throw new UnsupportedOperationException
		}
	}

	protected def dispatch Expr<? extends Type> toExpr(ArrayWithExpression expression) {
		val array = ExprUtils.cast(expression.operand.toExpr, ArrayType) as Expr<ArrayType<Type, Type>>
		val elem = expression.value.toExpr

		val parameters = expression.parameters
		if (parameters.size == 0) {
			throw new UnsupportedOperationException
		} else if (parameters.size == 1) {
			val parameter = expression.parameters.get(0)
			val index = parameter.toExpr
			Write(array, index, elem)
		} else {
			throw new UnsupportedOperationException
		}
	}

	protected def dispatch Expr<? extends Type> toExpr(IfThenElseExpression expression) {
		val cond = ExprUtils.cast(expression.condition.toExpr, BoolType)
		val then = expression.then.toExpr
		val elze = expression.^else.toExpr
		Ite(cond, then, elze)
	}

	protected def dispatch Expr<? extends Type> toExpr(ReferenceExpression expression) {
		val decl = expression.declaration.transform
		decl.ref
	}
	
}