package hu.bme.mit.inf.ttmc.code.ast;

import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;

public class FunctionCallExpressionAst extends ExpressionAst {

	private String name;
	private List<ExpressionAst> params;
	
	// @todo Function pointer
	public FunctionCallExpressionAst(String name, List<ExpressionAst> params) {
		this.name = name;
		this.params = params;
	}
	
	public String getName() {
		return this.name;
	}
	
	public List<ExpressionAst> getParams() {
		return this.params;
	}
	
	
	@Override
	public <E> E accept(ExpressionVisitor<E> visitor) {
		return visitor.visit(this);
	}

	@Override
	public AstNode[] getChildren() {
		return this.params.toArray(new AstNode[this.params.size()]);
	}

}
