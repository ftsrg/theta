package hu.bme.mit.inf.ttmc.code.simplifier;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.AstNode;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class StatementListAst extends StatementAst {
	
	private List<StatementAst> stmts = new ArrayList<>();

	public StatementListAst(List<StatementAst> stmts) {
		this.stmts = stmts;
	}
	
	public List<StatementAst> getStatements() {
		return this.stmts;
	}
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		throw new UnsupportedOperationException();
	}

	@Override
	public StatementAst copy() {
		throw new UnsupportedOperationException();
	}

	@Override
	public AstNode[] getChildren() {
		throw new UnsupportedOperationException();
	}
}