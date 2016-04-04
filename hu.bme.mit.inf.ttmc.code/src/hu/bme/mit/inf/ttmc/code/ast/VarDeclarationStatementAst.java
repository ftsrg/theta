package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class VarDeclarationStatementAst extends StatementAst {

	private String name;
	private VarDeclarationAst decl;
	
	public VarDeclarationStatementAst(VarDeclarationAst decl) {
		this.decl = decl;
		this.name = decl.getName();
	}

	public VarDeclarationAst getDeclaration() {
		return this.decl;
	}
	
	public String getName() {
		return this.name;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.decl };
	}
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}
	
}
