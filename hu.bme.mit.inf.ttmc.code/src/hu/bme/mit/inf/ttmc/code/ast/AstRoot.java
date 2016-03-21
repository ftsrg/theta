package hu.bme.mit.inf.ttmc.code.ast;

import java.util.List;

public class AstRoot extends AstNode {

	private List<FunctionAst> functions;
	
	public AstRoot(List<FunctionAst> functions) {
		this.functions = functions;
	}

	@Override
	public AstNode[] getChildren() {
		return this.functions.toArray(new AstNode[this.functions.size()]);
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
}
