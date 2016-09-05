package hu.bme.mit.inf.theta.code.ast;

import hu.bme.mit.inf.theta.code.ast.visitor.ExpressionVisitor;

public class UnaryExpressionAst extends ExpressionAst {

	private Operator operator;
	private ExpressionAst operand;
	
	public enum Operator {
		OP_PREFIX_INCR, OP_PREFIX_DECR, OP_POSTFIX_INCR, OP_POSTFIX_DECR, OP_ASTERISK, OP_PLUS, OP_MINUS, OP_NOT
	}
	
	public UnaryExpressionAst(ExpressionAst operand, Operator operator) {
		this.operand = operand;
		this.operator = operator;
	}
	
	public UnaryExpressionAst with(ExpressionAst operand) {
		if (operand == this.operand)
			return this;
		
		return new UnaryExpressionAst(operand, this.operator);
	}
	
	public Operator getOperator() {
		return this.operator;
	}
	
	public ExpressionAst getOperand() {
		return this.operand;
	}
	
	@Override
	public <E> E accept(ExpressionVisitor<E> visitor) {
		return visitor.visit(this);
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.operand };
	}

	@Override
	public ExpressionAst copy() {
		return new UnaryExpressionAst(this.operand.copy(), this.operator);
	}

}
