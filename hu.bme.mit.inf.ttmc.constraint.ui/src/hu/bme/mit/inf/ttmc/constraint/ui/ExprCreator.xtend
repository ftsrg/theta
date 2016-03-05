package hu.bme.mit.inf.ttmc.constraint.ui

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager
import hu.bme.mit.inf.ttmc.constraint.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory
import hu.bme.mit.inf.ttmc.constraint.model.AddExpression
import hu.bme.mit.inf.ttmc.constraint.model.AndExpression
import hu.bme.mit.inf.ttmc.constraint.model.ArrayAccessExpression
import hu.bme.mit.inf.ttmc.constraint.model.ArrayTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.ArrayWithExpression
import hu.bme.mit.inf.ttmc.constraint.model.BooleanTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.DecimalLiteralExpression
import hu.bme.mit.inf.ttmc.constraint.model.DivExpression
import hu.bme.mit.inf.ttmc.constraint.model.DivideExpression
import hu.bme.mit.inf.ttmc.constraint.model.EqualExpression
import hu.bme.mit.inf.ttmc.constraint.model.EqualityExpression
import hu.bme.mit.inf.ttmc.constraint.model.Expression
import hu.bme.mit.inf.ttmc.constraint.model.FalseExpression
import hu.bme.mit.inf.ttmc.constraint.model.FunctionTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.GreaterEqualExpression
import hu.bme.mit.inf.ttmc.constraint.model.GreaterExpression
import hu.bme.mit.inf.ttmc.constraint.model.ImplyExpression
import hu.bme.mit.inf.ttmc.constraint.model.InequalityExpression
import hu.bme.mit.inf.ttmc.constraint.model.IntegerLiteralExpression
import hu.bme.mit.inf.ttmc.constraint.model.IntegerTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.LessEqualExpression
import hu.bme.mit.inf.ttmc.constraint.model.LessExpression
import hu.bme.mit.inf.ttmc.constraint.model.ModExpression
import hu.bme.mit.inf.ttmc.constraint.model.MultiplyExpression
import hu.bme.mit.inf.ttmc.constraint.model.NotExpression
import hu.bme.mit.inf.ttmc.constraint.model.OrExpression
import hu.bme.mit.inf.ttmc.constraint.model.RationalLiteralExpression
import hu.bme.mit.inf.ttmc.constraint.model.RealTypeDefinition
import hu.bme.mit.inf.ttmc.constraint.model.SubtractExpression
import hu.bme.mit.inf.ttmc.constraint.model.TrueExpression
import hu.bme.mit.inf.ttmc.constraint.model.TypeReference
import hu.bme.mit.inf.ttmc.constraint.model.UnaryMinusExpression
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType
import hu.bme.mit.inf.ttmc.constraint.type.BoolType
import hu.bme.mit.inf.ttmc.constraint.type.IntType
import hu.bme.mit.inf.ttmc.constraint.type.RatType
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeInferrer

import static com.google.common.base.Preconditions.checkNotNull

class ExprCreator {
	
	protected val ConstraintManager manager
	
	protected val extension ExprFactory ef
	protected val extension TypeFactory tf
	
	protected val extension TypeInferrer inferrer
	
	new(ConstraintManager manager) {
		checkNotNull(manager);
		
		this.manager = manager
		
		ef = manager.exprFactory
		tf = manager.typeFactory
		
		inferrer = new TypeInferrer(manager)
	}
	
	protected def <T extends Type> Expr<? extends T> withType(Expr<? extends Type> expr, Class<T> metaType) {
		if (metaType.isInstance(getType(expr))) {
			expr as Expr<? extends T>
		} else {
			throw new Exception("Expression " + expr + " is not of type " + metaType.name)
		}
	}
	
	/////
	
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
		val ops = expression.operands.map[toExpr.withType(ClosedUnderAdd)]
		Add(ops)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(MultiplyExpression expression) {
		val ops = expression.operands.map[toExpr.withType(ClosedUnderMul)]
		Mul(ops)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(UnaryMinusExpression expression) {
		val op = expression.operand.toExpr.withType(ClosedUnderNeg)
		Neg(op)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(SubtractExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(ClosedUnderSub)
		val rightOp = expression.rightOperand.toExpr.withType(ClosedUnderSub)
		Sub(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(DivideExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(RatType)
		val rightOp = expression.rightOperand.toExpr.withType(RatType)
		RatDiv(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(DivExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(IntType)
		val rightOp = expression.rightOperand.toExpr.withType(IntType)
		IntDiv(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(ModExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(IntType)
		val rightOp = expression.rightOperand.toExpr.withType(IntType)
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
		val leftOp = expression.leftOperand.toExpr.withType(RatType)
		val rightOp = expression.rightOperand.toExpr.withType(RatType)
		Lt(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(LessEqualExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(RatType)
		val rightOp = expression.rightOperand.toExpr.withType(RatType)
		Leq(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(GreaterExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(RatType)
		val rightOp = expression.rightOperand.toExpr.withType(RatType)
		Gt(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(GreaterEqualExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(RatType)
		val rightOp = expression.rightOperand.toExpr.withType(RatType)
		Geq(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(NotExpression expression) {
		val op = expression.operand.toExpr.withType(BoolType)
		Not(op)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(ImplyExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(BoolType)
		val rightOp = expression.rightOperand.toExpr.withType(BoolType)
		Imply(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(EqualExpression expression) {
		val leftOp = expression.leftOperand.toExpr.withType(BoolType)
		val rightOp = expression.rightOperand.toExpr.withType(BoolType)
		Iff(leftOp, rightOp)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(AndExpression expression) {
		val ops = expression.operands.map[toExpr.withType(BoolType)]
		And(ops)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(OrExpression expression) {
		val ops = expression.operands.map[toExpr.withType(BoolType)]
		Or(ops)
	}
	
	protected def dispatch Expr<? extends Type> toExpr(ArrayAccessExpression expression) {
		val array = expression.operand.toExpr.withType(ArrayType) as Expr<ArrayType<Type, Type>>
		
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
		val array = expression.operand.toExpr.withType(ArrayType) as Expr<ArrayType<Type, Type>>
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
	
	/////
	
	protected def dispatch Type toType(TypeReference type) {
		type.reference.type.toType
	}
	
	protected def dispatch Type toType(BooleanTypeDefinition type) {
		Bool
	}
	
	protected def dispatch Type toType(IntegerTypeDefinition type) {
		Int
	}
	
	protected def dispatch Type toType(RealTypeDefinition type) {
		Rat
	}
	
	protected def dispatch Type toType(FunctionTypeDefinition type) {
		val parameterTypes = type.parameterTypes
		if (parameterTypes.size == 0) {
			throw new UnsupportedOperationException("TODO")
		} if (parameterTypes.size == 1) {
			val paramType = parameterTypes.get(0).toType
			val resultType = type.returnType.toType
			Func(paramType, resultType)
		} else {
			throw new UnsupportedOperationException("TODO")
		}
	}
	
	protected def dispatch Type toType(ArrayTypeDefinition type) {
		val indexTypes = type.indexTypes
		if (indexTypes.size == 0) {
			throw new UnsupportedOperationException("TODO")
		} if (indexTypes.size == 1) {
			val indexType = indexTypes.get(0).toType
			val elemType = type.elementType.toType
			Array(indexType, elemType)
		} else {
			throw new UnsupportedOperationException("TODO")
		}
	}
	
	
}