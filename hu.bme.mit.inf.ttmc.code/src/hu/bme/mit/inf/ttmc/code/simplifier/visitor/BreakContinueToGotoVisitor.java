package hu.bme.mit.inf.ttmc.code.simplifier.visitor;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.simplifier.SimplifyAstVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.StatementListAst;

public class BreakContinueToGotoVisitor extends SimplifyAstVisitor {
		
	private int loopId = 0;	
	private int breakCount = 0;
	private int contCount = 0;
	
	@Override
	public StatementAst visit(WhileStatementAst ast) {
		StatementAst newBody = ast.getBody().accept(this);
		if (this.breakCount == 0 && this.contCount == 0) // There were no break statements
			return ast;
		
		if (newBody instanceof CompoundStatementAst) {
			((CompoundStatementAst) newBody).getStatements().add(new LabeledStatementAst(String.format("LOOP%d_CONT", loopId), new NullStatementAst()));
		} else {
			List<StatementAst> statementList = new ArrayList<>();
			statementList.add(newBody);
			statementList.add(new LabeledStatementAst(String.format("LOOP%d_CONT", loopId), new NullStatementAst()));
			
			newBody = new CompoundStatementAst(statementList);
			ast = new WhileStatementAst(ast.getCondition(), newBody);			
		}
		
		List<StatementAst> stmts = new ArrayList<StatementAst>();
		
		stmts.add(new WhileStatementAst(ast.getCondition().accept(this), newBody));
		stmts.add(new LabeledStatementAst(String.format("LOOP%d_END", loopId), new NullStatementAst()));

		this.contCount = 0;
		this.breakCount = 0;
		this.loopId++;
		
		return new StatementListAst(stmts);
	}
	
	
	@Override
	public StatementAst visit(BreakStatementAst ast) {
		this.breakCount++;
		return new GotoStatementAst(String.format("LOOP%d_END", loopId));
	}
	
	public StatementAst visit(ContinueStatementAst ast) {
		this.contCount++;
		return new GotoStatementAst(String.format("LOOP%d_CONT", loopId));
	}
		
}
