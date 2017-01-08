package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.ExpressionVisitor;

public class CastExpressionAst extends ExpressionAst {

	private TypeNameAst typeName;
	private ExpressionAst operand;
	
	public CastExpressionAst(TypeNameAst typeName, ExpressionAst operand) {
		this.typeName = typeName;
		this.operand = operand;
	}

	@Override
	public <E> E accept(ExpressionVisitor<E> visitor) {
		return visitor.visit(this);
	}

	@Override
	public ExpressionAst copy() {
		throw new UnsupportedOperationException();
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.typeName, this.operand };
	}
	
	public TypeNameAst getTypeName() {
		return typeName;
	}

	public ExpressionAst getOperand() {
		return operand;
	}


}
