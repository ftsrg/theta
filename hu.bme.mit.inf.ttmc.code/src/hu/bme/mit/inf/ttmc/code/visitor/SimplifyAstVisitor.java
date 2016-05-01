package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.CloneAstVisitor;

public class SimplifyAstVisitor extends CloneAstVisitor {

	private StatementAstTransformerVisitor[] statementVisitors;
	
	public SimplifyAstVisitor() {
		this.statementVisitors = new StatementAstTransformerVisitor[] {
			new ForToWhileStatementVisitor(),
			new SwitchToIfElseVisitor(),
			new UnrollDeclarationsVisitor(),
			new BreakContinueToGotoVisitor(),
		};
	}
	
	@Override
	public StatementAst visit(CompoundStatementAst ast) {
		List<StatementAst> stmts = new ArrayList<>();
		for (StatementAst stmt : ast.getStatements()) {
			StatementAst res = stmt.accept(this);
			for (StatementAstTransformerVisitor visitor : this.statementVisitors) {
				res = res.accept(visitor);
			}
			
			if (res instanceof StatementAstTransformerVisitor.StatementListAst) {
				stmts.addAll(((StatementAstTransformerVisitor.StatementListAst) res).getStatements());
			} else {				
				stmts.add(res);
			}
		}
		
		return new CompoundStatementAst(stmts);
	}
	
	@Override
	public StatementAst visit(BreakStatementAst ast) {
		StatementAst res = ast;

		for (StatementAstTransformerVisitor visitor : this.statementVisitors) {
			res = res.accept(visitor);
		}

		return res;
	}
	
	@Override
	public StatementAst visit(ContinueStatementAst ast) {
		StatementAst res = ast;

		for (StatementAstTransformerVisitor visitor : this.statementVisitors) {
			res = res.accept(visitor);
		}

		return res;
	}
	
}
