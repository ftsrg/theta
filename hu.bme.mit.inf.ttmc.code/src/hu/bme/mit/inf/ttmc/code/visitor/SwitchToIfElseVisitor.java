package hu.bme.mit.inf.ttmc.code.visitor;

import java.lang.Thread.State;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;

public class SwitchToIfElseVisitor extends StatementAstTransformerVisitor {

	private static int uniqId = 0;
	private static int switchId = 0;
	
	@Override
	public StatementAst visit(SwitchStatementAst ast) {
		int id = switchId++;
		
		ExpressionAst expr = ast.getExpression();
		
		if (!(ast.getBody() instanceof CompoundStatementAst)) {
			throw new UnsupportedOperationException();
		}
		
		CompoundStatementAst body = (CompoundStatementAst) ast.getBody();	
		List<StatementAst> stmts = new ArrayList<>();
				
		LinkedHashMap<ExpressionAst, String> conditionLabels = new LinkedHashMap<>(); // We need to retain order

		// First iteration: Find conditions
		boolean hasDefault = false;
		
		for (StatementAst stmt : body.getStatements()) {
			if (stmt instanceof CaseStatementAst) {
				CaseStatementAst caseStmt = (CaseStatementAst) stmt;
				conditionLabels.put(caseStmt.getExpression(), String.format("SW%d_COND_%d", id, uniqId++));								
			}
			
			if (stmt instanceof DefaultStatementAst) {
				hasDefault = true;
				break; // Our work here is done
			}
		}
		
		// Create the if statements for each condition
		for (Map.Entry<ExpressionAst, String> entry : conditionLabels.entrySet()) {
			ExpressionAst cond = new BinaryExpressionAst(expr, entry.getKey(), BinaryExpressionAst.Operator.OP_IS_EQ);
			IfStatementAst ifStmt = new IfStatementAst(cond, new GotoStatementAst(entry.getValue()));
			
			stmts.add(ifStmt);
		}

		String defLabel = String.format("SW%d_DEF", id);
		String endLabel = String.format("SW%d_END", id);
		String initLabel = String.format("SW%d_INIT", id);

		String currentLabel = initLabel;
		
		stmts.add(new GotoStatementAst(defLabel));
		
		LinkedHashMap<String, List<StatementAst>> caseStatements = new LinkedHashMap<>();
		
		caseStatements.put(currentLabel, new ArrayList<>());
		
		boolean isBroken = true;
		
		for (StatementAst stmt : body.getStatements()) {
			List<StatementAst> currentBlock = caseStatements.get(currentLabel);
			
			// If we see a case statement, find the label
			if (stmt instanceof CaseStatementAst) {
				CaseStatementAst caseStmt = (CaseStatementAst) stmt;
				String target = conditionLabels.get(caseStmt.getExpression());
				
				if (!isBroken) { // If there is no break statement, we need to jump to the other conditional's label
					currentBlock.add(new GotoStatementAst(target));
				} else { // If this is after a break statement, we need to change the current label
					currentLabel = target;
					List<StatementAst> newBlock = new ArrayList<>();
					newBlock.add(new LabeledStatementAst(target, new NullStatementAst()));
					
					caseStatements.put(target, newBlock);
				}
			} else if (stmt instanceof BreakStatementAst) {
				isBroken = true;
				currentBlock.add(new GotoStatementAst(endLabel));
			} else if (hasDefault && stmt instanceof DefaultStatementAst)  {
				if (!isBroken) { // If there was no break, we need to append a GOTO DEFAULT; to the current blcok
					currentBlock.add(new GotoStatementAst(defLabel));
				}

				currentLabel = defLabel;
				List<StatementAst> newBlock = new ArrayList<>();
				newBlock.add(new LabeledStatementAst(defLabel, new NullStatementAst()));
				
				caseStatements.put(defLabel, newBlock);
			} else {
				currentBlock.add(stmt);
			}
		}
		
		if (!hasDefault) {
			stmts.add(new LabeledStatementAst(defLabel, new NullStatementAst()));
		}
		
		stmts.addAll(0, caseStatements.get(initLabel));
		
		for (List<StatementAst> stmtList : caseStatements.values()) {
			stmts.addAll(stmtList);
		}
		stmts.add(new LabeledStatementAst(endLabel, new NullStatementAst()));
		
		return new CompoundStatementAst(stmts);
	}
	
	
	
}
