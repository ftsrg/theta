package hu.bme.mit.inf.ttmc.code.ast;

public class BinaryExpressionAst extends ExpressionAst {

	public enum Operator {
		OP_ADD, OP_SUB, OP_MUL, OP_DIV, OP_ASSIGN, OP_IS_EQUAL, OP_IS_GTEQ, OP_IS_LTEQ, OP_IS_LT, OP_IS_GT
	}
	
	private Operator operator;
	private ExpressionAst left;
	private ExpressionAst right;
	
	public BinaryExpressionAst(ExpressionAst left, ExpressionAst right, Operator operator) {
		this.operator = operator;
		this.left = left;
		this.right = right;
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
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
}
