package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;

public class BinaryExpressionAst extends ExpressionAst {

	public enum Operator {
		OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_MOD, // Arithmetic operators
		OP_ASSIGN, // Assignment
		OP_ADD_ASSIGN, OP_SUB_ASSIGN, OP_MUL_ASSIGN, OP_DIV_ASSIGN, OP_MOD_ASSIGN, // Arithmetic assignment
		OP_IS_EQ, OP_IS_GTEQ, OP_IS_LTEQ, OP_IS_LT, OP_IS_GT, OP_IS_NOT_EQ, // Comparison
		OP_LOGIC_AND, OP_LOGIC_OR // Logical
	}
	
	private Operator operator;
	private ExpressionAst left;
	private ExpressionAst right;
	
	public BinaryExpressionAst(ExpressionAst left, ExpressionAst right, Operator operator) {
		this.operator = operator;
		this.left = left;
		this.right = right;
	}
	
	public BinaryExpressionAst with(ExpressionAst left, ExpressionAst right)
	{
		if (left == this.left && right == this.right)
			return this;
		
		return new BinaryExpressionAst(left, right, this.operator);
	}
	
	public Operator getOperator() {
		return this.operator;
	}
	
	public ExpressionAst getLeft() {
		return this.left;
	}
	
	public ExpressionAst getRight() {
		return this.right;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {left, right};
	}
	
	@Override
	public <E> E accept(ExpressionVisitor<E> visitor) {
		return visitor.visit(this);
	}

	@Override
	public ExpressionAst copy() {
		return new BinaryExpressionAst(this.left.copy(), this.right.copy(), this.operator);
	}
	
	
}
