package hu.bme.mit.inf.ttmc.frontend.ir.expr;

import hu.bme.mit.inf.ttmc.frontend.ir.type.ValueType;

public class BinaryExpression implements Expression {

	public enum BinaryOperator {
		OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_MOD,
		OP_AND, OP_OR,
		OP_LSL, OP_LSR, OP_BITAND, OP_BITOR, OP_BITXOR
	}

	private Expression left;
	private Expression right;
	private BinaryOperator operator;

	public BinaryExpression(Expression left, Expression right, BinaryOperator operator) {
		this.left = left;
		this.right = right;
		this.operator = operator;
	}




}
