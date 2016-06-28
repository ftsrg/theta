package hu.bme.mit.inf.ttmc.code.ast;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclaratorVisitor;

public class FunctionDeclaratorAst extends DeclaratorAst {

	private List<ParameterDeclarationAst> params = new ArrayList<>();
	
	public FunctionDeclaratorAst(String name, List<ParameterDeclarationAst> params) {
		super(name);
		this.params = params;
	}
	
	public List<ParameterDeclarationAst> getParameters() {
		return this.params;
	}
		
	@Override
	public AstNode[] getChildren() {
		return this.params.toArray(new AstNode[this.params.size()]);
	}

	@Override
	public FunctionDeclaratorAst copy() {
		return new FunctionDeclaratorAst(this.getName(), this.params);
	}

	@Override
	public <DR> DR accept(DeclaratorVisitor<DR> visitor) {
		return visitor.visit(this);
	}
	

}
