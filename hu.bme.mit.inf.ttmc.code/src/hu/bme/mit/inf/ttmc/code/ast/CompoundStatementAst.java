package hu.bme.mit.inf.ttmc.code.ast;

import java.util.List;

public class CompoundStatementAst extends StatementAst {

	private List<StatementAst> statements;
	
	public CompoundStatementAst(List<StatementAst> statements) {
		this.statements = statements;
	}
	
	public List<StatementAst> getStatements() {
		return this.statements;
	}

	@Override
	public AstNode[] getChildren() {
		return this.statements.toArray(new AstNode[this.statements.size()]);
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
	
	
}
