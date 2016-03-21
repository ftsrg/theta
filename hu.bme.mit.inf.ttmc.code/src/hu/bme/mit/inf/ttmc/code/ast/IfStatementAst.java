package hu.bme.mit.inf.ttmc.code.ast;

public class IfStatementAst extends StatementAst {

	private ExpressionAst condition;
	private StatementAst thenStatement;
	private StatementAst elseStatement;
	
	public IfStatementAst(ExpressionAst condition, StatementAst thenStatement, StatementAst elseStatement) {
		this.condition = condition;
		this.thenStatement = thenStatement;
		this.elseStatement = elseStatement;
	}
	
	public IfStatementAst(ExpressionAst condition, StatementAst thenStatement) {
		this.condition = condition;
		this.thenStatement = thenStatement;
	}
	
	@Override
	public AstNode[] getChildren() {
		if (this.elseStatement != null) {
			return new AstNode[] { condition, thenStatement, elseStatement };
		} else {
			return new AstNode[] { condition, thenStatement };
		}
	}

}
