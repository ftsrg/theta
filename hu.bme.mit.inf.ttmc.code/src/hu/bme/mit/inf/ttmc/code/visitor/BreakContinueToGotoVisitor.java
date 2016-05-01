package hu.bme.mit.inf.ttmc.code.visitor;



import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.visitor.ast.TransformedWhileStatementAst;

public class BreakContinueToGotoVisitor extends StatementAstTransformerVisitor {
	
	private int loopId = 0;	
	private int breakCount = 0;
	private int contCount = 0;
	private Stack<Integer> loops = new Stack<>();
		
	@Override
	public StatementAst visit(WhileStatementAst ast) {
		if (this.breakCount == 0 && this.contCount == 0) // There were no break statements
			return ast;
		
		StatementAst body = ast.getBody();
		
		if (this.contCount != 0) {
			// We need to append the required instruction
			if (body instanceof CompoundStatementAst) {
				((CompoundStatementAst) body).getStatements().add(new LabeledStatementAst(String.format("LOOP%d_CONT", loopId), new NullStatementAst()));
			} else {
				List<StatementAst> statementList = new ArrayList<>();
				statementList.add(body);
				statementList.add(new LabeledStatementAst(String.format("LOOP%d_CONT", loopId), new NullStatementAst()));
				
				body = new CompoundStatementAst(statementList);
				ast = new WhileStatementAst(ast.getCondition(), body);
			}
		}
		
		List<StatementAst> stmts = new ArrayList<>();
		stmts.add(ast);
		
		if (this.breakCount != 0) {
			stmts.add(new LabeledStatementAst(String.format("LOOP%d_END", loopId), new NullStatementAst()));			
		}

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
