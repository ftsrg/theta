package hu.bme.mit.inf.ttmc.code.ast;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

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
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public CompoundStatementAst copy() {
		List<StatementAst> stmts = new ArrayList<>();
		
		for (StatementAst stmt : this.statements) {
			stmts.add(stmt.copy());
		}
		
		return new CompoundStatementAst(stmts);
	}
	
	
	
}
