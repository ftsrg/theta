package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.StatementVisitor;

public class DeclarationStatementAst extends StatementAst {

	private DeclarationAst decl;

	public DeclarationStatementAst(DeclarationAst decl) {
		this.decl = decl;
	}

	public DeclarationStatementAst with(DeclarationAst decl) {
		if (decl == this.decl)
			return this;

		return new DeclarationStatementAst(decl);
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
