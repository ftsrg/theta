package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class DeclarationStatementAst extends StatementAst {

	private DeclarationAst decl;
	
	public DeclarationStatementAst(DeclarationAst decl) {
		this.decl = decl;
	}

	public DeclarationAst getDeclaration() {
		return this.decl;
	}
		
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.decl };
	}
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public DeclarationStatementAst copy() {
		return new DeclarationStatementAst(decl.copy());
	}
	
}
