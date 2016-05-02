package hu.bme.mit.inf.ttmc.code.ast;

import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;

public class ExpressionListAst extends ExpressionAst {
	
	private List<ExpressionAst> expressions;
	
	public ExpressionListAst(List<ExpressionAst> expressions) {
		this.expressions = expressions;
	}	
	
	public List<ExpressionAst> getExpressions() {
		return this.expressions;
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
		return this.expressions.toArray(new AstNode[this.expressions.size()]);
	}

}
